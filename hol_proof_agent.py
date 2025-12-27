#!/usr/bin/env python3
"""
HOL4 Proof Development Agent

Autonomous agent using Claude Agent SDK + MCP server for HOL4 interaction.

SYSTEM RECOVERY PROMPT
======================
If this codebase is lost, use the following to reconstruct it:

Build an autonomous HOL4 theorem proving agent with these components:

Architecture
------------
hol_proof_agent.py (orchestrator)
  -> spawns via claude-agent-sdk
Claude Code CLI (with MCP server connected)
  -> MCP protocol (stdio)
hol_mcp_server.py (FastMCP, in-memory session registry)
  -> owns HOL subprocess (stdin/stdout pipes)

Components
----------
1. hol_mcp_server.py (FastMCP)
   Tools (all take session:str):
   - hol_start(workdir, name) -> Start or reconnect HOL session (idempotent, returns top_goals())
   - hol_sessions() -> List active sessions (name, workdir, age, status)
   - hol_send(session, command, timeout=5) -> Send SML, return output
   - hol_interrupt(session) -> SIGINT to process group
   - hol_stop(session) -> SIGTERM + wait
   - hol_restart(session) -> Stop + start (preserves workdir)
   - holmake(workdir, target="", timeout=90) -> Run Holmake --qof

   Cursor tools (RECOMMENDED entry point):
   - hol_cursor_init(file, session="default", workdir=None) -> Auto-start session, parse file, enter goaltree for first cheat
   - hol_cursor_complete(session) -> Extract p(), splice into file, advance, enter goaltree for next
   - hol_cursor_status(session) -> Position, completed, remaining cheats
   - hol_cursor_reenter(session) -> Re-enter goaltree after drop() or to retry

   Registry: dict[str, tuple[HOLSession, datetime, Path]] in-memory only

2. hol_session.py
   HOLSession class:
   - __init__(workdir) -> store path
   - start() -> spawn hol --zero, start_new_session=True, load etq.sml + .hol_init.sml
   - send(sml, timeout) -> write sml+NUL, read until NUL, handle timeout with interrupt
   - interrupt() -> os.killpg(pgid, SIGINT)
   - stop() -> SIGTERM, await process.wait(), cleanup
   - is_running property
   - Null-byte framing for HOL --zero mode

3. hol_cursor.py + hol_file_parser.py
   ProofCursor: track position in file, completed theorems, remaining cheats
   - initialize() -> parse file, find first cheat, load HOL context up to it
   - start_current() -> gt `goal`, replay tactics_before_cheat via etq
   - complete_and_advance() -> get p(), splice_into_theorem(), next_cheat()

   TheoremInfo dataclass: name, kind, goal, start_line, has_cheat, tactics_before_cheat
   parse_theorems(content) -> list[TheoremInfo]
   splice_into_theorem(content, name, tactics) -> new content
   parse_p_output(output) -> tactic script string

4. hol_proof_agent.py (orchestrator)
   CLI: --task (required), --claude-md, --prompt, --fresh, --model, --max-messages

   Flow:
   1. Load state from .claude/hol_agent_state.json (session_id, counts, hol_session)
   2. Build system prompt with CLAUDE.md, task file, MCP tool docs
   3. Loop forever:
      a. Create ClaudeSDKClient with mcp_servers config pointing to hol_mcp_server.py
      b. Send prompt (new: read task for Handoff; resume: continue)
      c. Process messages, count AssistantMessage, save state after each
      d. Watch for PROOF_COMPLETE: in text -> exit success
      e. At max_messages: trigger handoff (commit, capture state, update task file)
      f. Clear session_id, preserve hol_session, loop

   Handoff prompt must include:
   - Commit progress (git add specific files only, never -A)
   - Update task file ## Handoff section with: what tried, what worked, next steps
     (goals/holmake are auto-injected at startup)
   - DO NOT stop HOL session

   Interrupt handling: Ctrl+C -> save state, prompt for input, 'q' to quit
   State file fields: session_id, message_count, session_message_count, hol_session

5. System prompt content
   - Complexity management (<100 lines visible state, chain tactics, helper lemmas)
   - Completion criteria: Holmake passes, no CHEAT/FAIL warnings
   - MCP tool documentation with examples
   - Goaltree mode: gt, etq, p(), backup(), top_goals(), drop()
   - Subgoal patterns: by, sg, suffices_by
   - Workflow: assess -> identify cheats -> debug interactively -> update file -> verify
   - Recovery: read task file, hol_start() to reconnect, holmake()

Dependencies: fastmcp>=2.0.0, claude-agent-sdk>=0.1.0

Key Invariants
--------------
1. HOL sessions survive handoffs (context clearing), NOT orchestrator restarts
2. Explicit session names (not directory-keyed)
3. All HOL interaction via MCP tools (no direct Bash to HOL)
4. Handoff preserves session name for next Claude context (same MCP server)
5. Agent runs forever until PROOF_COMPLETE
"""

import asyncio
import glob
import json
import os
import re
import shlex
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Optional

from claude_agent_sdk import (
    ClaudeAgentOptions,
    ClaudeSDKClient,
    PermissionResultAllow,
    PermissionResultDeny,
    ResultMessage,
)

# Import MCP server instance - allows HOL sessions to persist across handoffs
from hol_mcp_server import mcp as hol_mcp, _sessions, hol_sessions, hol_send, holmake


# =============================================================================
# Bash Restriction
# =============================================================================

# Allowed git subcommands
ALLOWED_GIT_SUBCOMMANDS = {
    "add", "commit", "reset",  # Write
    "status", "diff", "log", "show", "branch",  # Read-only
    "ls-tree", "rev-parse", "cat-file", "merge-base",
}


def is_allowed_command(cmd: str) -> bool:
    """Check if command is in allowlist. Rejects command chaining."""
    # Reject commands with shell operators (chaining, piping)
    if re.search(r'[;&|`$()]', cmd):
        return False

    try:
        tokens = shlex.split(cmd)
    except ValueError:
        return False

    if not tokens:
        return False

    prog = tokens[0]

    # Git commands only - use holmake MCP tool for Holmake
    if prog == "git" and len(tokens) >= 2:
        return tokens[1] in ALLOWED_GIT_SUBCOMMANDS

    return False


async def tool_permission(tool_name: str, tool_input: dict, agent_context) -> PermissionResultAllow | PermissionResultDeny:
    """Restrict Bash to allowed commands. All HOL interaction via MCP."""
    if tool_name != "Bash":
        return PermissionResultAllow()
    cmd = tool_input.get("command", "")
    if is_allowed_command(cmd):
        return PermissionResultAllow()
    print(f"  [DENIED] Bash: {cmd}")
    return PermissionResultDeny("Bash restricted. Use MCP tools for HOL interaction.")


# =============================================================================
# Configuration
# =============================================================================

@dataclass
class AgentConfig:
    """Configuration for the HOL proof agent."""
    working_dir: str
    task_file: str
    claude_md: str
    model: str = "claude-opus-4-20250514"
    max_consecutive_errors: int = 5
    max_agent_messages: int = 100
    fresh: bool = False

    @property
    def state_path(self) -> str:
        return os.path.join(self.working_dir, ".claude", "hol_agent_state.json")


@dataclass
class AgentState:
    """Persisted agent state for resume."""
    path: str
    session_id: Optional[str] = None
    message_count: int = 0
    session_message_count: int = 0
    hol_session: Optional[str] = None  # HOL session name (key into _sessions)
    holmake_env: Optional[dict] = None  # env vars for holmake
    # Usage tracking
    input_tokens: int = 0
    output_tokens: int = 0
    cache_creation_tokens: int = 0
    cache_read_tokens: int = 0
    total_cost_usd: float = 0.0

    def add_usage(self, usage: dict, cost: float) -> None:
        """Accumulate token usage from ResultMessage."""
        self.input_tokens += usage.get("input_tokens", 0)
        self.output_tokens += usage.get("output_tokens", 0)
        self.cache_creation_tokens += usage.get("cache_creation_input_tokens", 0)
        self.cache_read_tokens += usage.get("cache_read_input_tokens", 0)
        self.total_cost_usd += cost

    def usage_summary(self) -> str:
        """Return formatted usage string with cache hit rate."""
        total_input = self.input_tokens + self.cache_creation_tokens + self.cache_read_tokens
        cache_rate = (self.cache_read_tokens / total_input * 100) if total_input > 0 else 0.0
        return (
            f"In: {self.input_tokens:,} | Out: {self.output_tokens:,} | "
            f"Cache: {cache_rate:.1f}% | ${self.total_cost_usd:.2f}"
        )

    def save(self) -> None:
        with open(self.path, 'w') as f:
            json.dump({
                "session_id": self.session_id,
                "message_count": self.message_count,
                "session_message_count": self.session_message_count,
                "hol_session": self.hol_session,
                "holmake_env": self.holmake_env,
                "input_tokens": self.input_tokens,
                "output_tokens": self.output_tokens,
                "cache_creation_tokens": self.cache_creation_tokens,
                "cache_read_tokens": self.cache_read_tokens,
                "total_cost_usd": self.total_cost_usd,
            }, f)

    @classmethod
    def load(cls, path: str) -> "AgentState":
        try:
            with open(path) as f:
                data = json.load(f)
                return cls(
                    path=path,
                    session_id=data.get("session_id"),
                    message_count=data.get("message_count", 0),
                    session_message_count=data.get("session_message_count", 0),
                    hol_session=data.get("hol_session"),
                    holmake_env=data.get("holmake_env"),
                    input_tokens=data.get("input_tokens", 0),
                    output_tokens=data.get("output_tokens", 0),
                    cache_creation_tokens=data.get("cache_creation_tokens", 0),
                    cache_read_tokens=data.get("cache_read_tokens", 0),
                    total_cost_usd=data.get("total_cost_usd", 0.0),
                )
        except Exception:
            return cls(path=path)


def read_file(path: str) -> str:
    """Read a file, return empty string on error."""
    try:
        with open(path, 'r') as f:
            return f.read()
    except Exception:
        return ""


def get_large_files(working_dir: str, byte_threshold: int = 15000, line_threshold: int = 500) -> list:
    """Find .sml files exceeding line threshold."""
    large = []
    for sml in glob.glob(os.path.join(working_dir, "**/*.sml"), recursive=True):
        try:
            if os.path.getsize(sml) < byte_threshold:
                continue
            with open(sml) as f:
                lines = sum(1 for _ in f)
            if lines > line_threshold:
                rel_path = os.path.relpath(sml, working_dir)
                large.append((rel_path, lines))
        except OSError:
            pass
    return sorted(large, key=lambda x: -x[1])


def build_system_prompt(config: AgentConfig) -> str:
    """Build static system prompt (cacheable across runs)."""
    claude_md = read_file(config.claude_md)
    mcp = "mcp__hol__"  # MCP tool prefix

    return f"""You are an autonomous HOL4 theorem proving agent. You run FOREVER until the proof is complete.

You have {config.max_agent_messages} assistant messages before context is cleared (handoff). Each response you send counts as one message, regardless of user input. Plan accordingly - make steady progress and document state before handoff.

## Complexity Management

**Never work with >100 lines of visible state.** If goals exceed this:
- Chain tactics (`>>`) to skip intermediate subgoals
- Extract helper lemmas - smaller proofs fit in context better
- Use `by` to prove subgoals inline and avoid proliferation
- Prefer multiple small lemmas over one giant proof
- Aim to keep files between 100-500 loc; if a file exceeds 500 loc, refactor

**Before proving:** Understand *why* it's true. Write a 2-3 sentence proof sketch.

**Performance:** Be mindful of proof performance:
- If a tactic takes >15 seconds, use hol_interrupt - do NOT wait
- `metis_tac` on large search space hangs - avoid or constrain
- `fs[recursive_def]` causes blowup - use `simp[Once def]` instead
- Test tactics individually before combining

## COMPLETION CRITERIA
The proof is complete when:
1. `holmake(workdir)` succeeds
2. NO "CHEAT" warnings in output
3. NO "FAIL" in output

When complete, output "PROOF_COMPLETE:" followed by a summary.

## CLAUDE.md Guidelines
{claude_md}

## MCP Tools

All HOL interaction via MCP tools (prefix: `{mcp}`). **Never use Bash for HOL.**

### {mcp}hol_start(workdir: str, name: str = "default") -> str
Start or reconnect HOL session. **Idempotent**: if session exists, returns top_goals().

### {mcp}hol_send(session: str, command: str, timeout: int = 5) -> str
Send SML to HOL. Returns output. Max timeout 600s.

### {mcp}hol_interrupt(session: str) -> str
Send SIGINT to abort runaway tactic. Use if command takes >15 seconds.

### {mcp}holmake(workdir: str, target: str = None, timeout: int = 90) -> str
Run Holmake --qof. Returns output + build logs on failure. Max timeout 1800s.

### {mcp}hol_sessions() -> str
List active sessions with workdir, age, status.

### {mcp}hol_restart(session: str) -> str
Restart session (stop + start, preserves workdir). Use when HOL state is corrupted.

### Cursor Tools (RECOMMENDED entry point)
- `{mcp}hol_cursor_init(file, session="default", workdir=None)` - Auto-start session, parse file, enter goaltree and show output of top_goals()
- `{mcp}hol_cursor_complete(session)` - Extract p(), splice into file, advance, enter goaltree for next
- `{mcp}hol_cursor_status(session)` - Show position: "3/7 theorems, current: foo_thm"
- `{mcp}hol_cursor_reenter(session)` - Re-enter goaltree after drop() or to retry

Cursor workflow: init → (prove → complete) × N → done

## Goaltree Mode (Interactive Proving)

Always use goaltree mode (`gt`/`etq`) - it records tactics for extraction:

| Command | Purpose |
|---------|---------|
| gt `tm` | Start proof (goaltree mode) |
| `etq "tac"` | Apply tactic (records for extraction) |
| `p()` | Show proof tree - copy directly to Theorem block |
| `b()` / `backup()` | Undo last tactic |
| `top_goals()` | List remaining goals |
| `drop()` | Abandon proof |

## Subgoal Patterns

- `'tm' by tac` - prove tm, add as assumption
- `sg 'tm' >- tac` - tm as subgoal, tac must close it
- `'tm' suffices_by tac` - prove tm => goal

## Theorem Search

DB.find "name" | DB.match [] ``pat`` | DB.theorems "thy"

## Workflow

1. **Assess**: `{mcp}holmake(workdir)` to see build state
2. **Start proving** (RECOMMENDED):
   - `{mcp}hol_cursor_init(file="path/to/file.sml")` - auto-starts session, enters goaltree for first cheat
   - Prove interactively with `{mcp}hol_send` (etq, p(), backup)
   - `{mcp}hol_cursor_complete(session="default")` - saves proof, advances, enters goaltree for next
   - Repeat until all theorems done
3. **Manual alternative** (for single theorems or advanced control):
   - `{mcp}hol_start(workdir, name="main")` - start session explicitly
   - `{mcp}hol_send(session="main", command='gt `goal`;')` - enter goaltree
   - Copy p() output to file manually via Edit
4. **Verify**: `{mcp}holmake(workdir)` again
5. **Iterate**: Until no cheats remain

## Critical Rules

1. NEVER GIVE UP - keep trying different approaches forever
2. If stuck on one approach for 10+ attempts, try a different strategy
3. Helper lemmas are your friend - break big proofs into smaller ones
4. `gvs[AllCaseEqs()]` can be too aggressive - sometimes `fs[]` or `simp[]` is better
5. For induction, make sure IH is applicable (check variable names)
6. If tactic runs >15 seconds, use hol_interrupt and try different approach
7. NEVER delete working proof code - if adding cheat, comment out original proof first
8. Periodically clean task file: delete outdated handoffs, stale notes, superseded info

## Recovery

If context seems lost:
1. Check ## Handoff section in first message above
2. `{mcp}hol_cursor_init(file)` - auto-starts session, positions at first cheat
3. `{mcp}holmake(workdir)` to see what's failing
4. `{mcp}hol_cursor_reenter(session)` to retry current theorem after drop()

BEGIN NOW.
"""


# =============================================================================
# Helpers
# =============================================================================

def print_message_blocks(message, prefix="  ") -> list[str]:
    """Print content blocks from a message. Returns list of text blocks."""
    texts = []
    if hasattr(message, 'content'):
        for block in message.content:
            if hasattr(block, 'name') and hasattr(block, 'input'):
                print(f"{prefix}[TOOL] {block.name}: {json.dumps(block.input)}")
            elif hasattr(block, 'tool_use_id'):
                content = getattr(block, 'content', None)
                if content:
                    # ToolResultBlock.content is str | list[dict] | None
                    if isinstance(content, str):
                        # SDK may wrap results as JSON: {"result": "..."}
                        try:
                            parsed = json.loads(content)
                            text = parsed.get('result', content) if isinstance(parsed, dict) else content
                        except json.JSONDecodeError:
                            text = content
                    elif isinstance(content, list):
                        # MCP returns [{"type": "text", "text": "..."}]
                        text = '\n'.join(item.get('text', str(item)) for item in content)
                    else:
                        text = str(content)
                    texts.append(text)  # Include tool output for session detection
                    print(f"{prefix}[TOOL OUTPUT]\n{text}")
                else:
                    print(f"{prefix}[TOOL OUTPUT] (none)")
            elif hasattr(block, 'text') and block.text:
                texts.append(block.text)
                print(f"{prefix}[TEXT] {block.text}")
    return texts


# =============================================================================
# Agent
# =============================================================================

# MCP server configuration - use SDK-managed instance for persistence across handoffs
# With type "sdk", the SDK uses our MCP instance but doesn't manage its lifecycle.
# This allows HOL sessions to survive when we exit/recreate SDK clients at handoff.
MCP_SERVER_CONFIG = {
    "hol": {
        "type": "sdk",
        "name": "hol",
        "instance": hol_mcp._mcp_server,
    }
}


async def run_agent(config: AgentConfig, initial_prompt: Optional[str] = None) -> bool:
    """Run the agent until completion."""

    system_prompt = build_system_prompt(config)
    error_count = 0
    os.makedirs(os.path.dirname(config.state_path), exist_ok=True)

    # Load previous state
    state = AgentState.load(config.state_path)

    print(f"[AGENT] Starting (handoff every {config.max_agent_messages} messages)...")

    while True:
        print(f"\n{'='*60}")
        if state.session_id:
            print(f"[SESSION] Resuming {state.session_id}")
        else:
            print(f"[SESSION] Starting new session")
        print(f"{'='*60}")

        try:
            opts = ClaudeAgentOptions(
                cwd=config.working_dir,
                model=config.model,
                system_prompt=system_prompt,
                allowed_tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob", "mcp__hol__*"],
                disallowed_tools=["TodoRead", "TodoWrite"],
                mcp_servers=MCP_SERVER_CONFIG,
                resume=state.session_id,
                can_use_tool=tool_permission,
            )

            async with ClaudeSDKClient(opts) as client:
                # Build prompt
                if state.session_id:
                    # Resuming SDK session - agent has context
                    prompt = initial_prompt or "Continue."
                else:
                    # New SDK session - include task file and context in first message
                    task = read_file(config.task_file)
                    init = read_file(os.path.join(config.working_dir, ".hol_init.sml"))

                    # Inject HOL state to save agent turns
                    hol_state = ""
                    try:
                        sessions_out = await hol_sessions.fn()
                        hol_state = f"\n\n[auto] hol_sessions():\n{sessions_out}\n"
                    except Exception as e:
                        hol_state = f"\n\n[auto] hol_sessions() error: {e}\n"

                    if not state.hol_session:
                        pass
                    elif state.hol_session not in _sessions:
                        hol_state += f"\n[auto] Session '{state.hol_session}' not found. See task file for workdir."
                        state.hol_session = None
                        state.save()
                    else:
                        entry = _sessions[state.hol_session]
                        workdir = str(entry.workdir)

                        if not entry.session.is_running:
                            hol_state += f"\n[auto] Session '{state.hol_session}' died. Restart: hol_start(\"{workdir}\")"
                        else:
                            try:
                                goals = await hol_send.fn(state.hol_session, "top_goals();", timeout=10)
                                hol_state += f"\n[auto] hol_send(\"{state.hol_session}\", \"top_goals();\"):\n{goals}"
                            except Exception as e:
                                hol_state += f"\n[auto] top_goals() error: {e}. Try hol_interrupt() or hol_restart()."

                        if entry.cursor:
                            status = entry.cursor.status
                            hol_state += f"\n\n[auto] hol_cursor_status(\"{state.hol_session}\"):\n"
                            hol_state += f"File: {status['file']}\n"
                            hol_state += f"Position: {status['position']}, Current: {status['current']} (line {status['current_line']})\n"
                            hol_state += f"Remaining cheats: {status['remaining_cheats']}"
                        else:
                            hol_state += f"\n\n[auto] hol_cursor_status(\"{state.hol_session}\"): (none)"

                        try:
                            # Prefer persisted env, fallback to in-memory
                            hm_env = state.holmake_env or entry.holmake_env
                            hm_out = await holmake.fn(workdir, env=hm_env, timeout=60)
                            hol_state += f"\n\n[auto] holmake(\"{workdir}\"):\n{hm_out}"
                        except Exception as e:
                            hol_state += f"\n\n[auto] holmake error: {e}"

                    prompt = f"## Task File: {config.task_file}\n{task}\n\n"
                    if init:
                        prompt += f"## .hol_init.sml\n{init}\n\n"

                    prompt += "Begin. Check ## Handoff section above for current state."
                    if state.hol_session:
                        prompt += f" Previous HOL session: '{state.hol_session}'."
                    prompt += hol_state
                    if initial_prompt:
                        prompt += f" {initial_prompt}"

                    large_files = get_large_files(config.working_dir)
                    if large_files:
                        file_list = ", ".join(f"{f} ({n} lines)" for f, n in large_files[:5])
                        prompt += f" WARNING: Large files (consider refactoring): {file_list}."

                print(f"[SEND] {prompt}")
                await client.query(prompt)

                # Capture session ID and save immediately
                if hasattr(client, 'session_id') and client.session_id and client.session_id != state.session_id:
                    state.session_id = client.session_id
                    print(f"[SESSION] ID: {state.session_id}")
                    state.save()

                # Process messages
                async for message in client.receive_messages():
                    msg_type = type(message).__name__
                    print(f"  [MSG TYPE] {msg_type}")

                    # Capture session_id from multiple sources
                    new_session_id = None
                    if hasattr(message, 'session_id') and message.session_id:
                        new_session_id = message.session_id
                    elif msg_type == "SystemMessage" and hasattr(message, 'data') and isinstance(message.data, dict):
                        new_session_id = message.data.get('session_id')

                    if new_session_id and state.session_id != new_session_id:
                        state.session_id = new_session_id
                        print(f"[SESSION] ID: {state.session_id}")
                        state.save()

                    # Count assistant messages
                    if msg_type == "AssistantMessage":
                        state.session_message_count += 1
                        state.message_count += 1
                        print(f"[MSG {state.session_message_count}/{config.max_agent_messages}] (total: {state.message_count})")
                        # Sync holmake_env from session entry
                        if state.hol_session and state.hol_session in _sessions:
                            entry_env = _sessions[state.hol_session].holmake_env
                            if entry_env != state.holmake_env:
                                state.holmake_env = entry_env
                        state.save()

                    # Log and check for completion
                    texts = print_message_blocks(message)
                    for text in texts:
                        if "PROOF_COMPLETE:" in text:
                            summary = text.split("PROOF_COMPLETE:")[-1].strip()
                            print(f"\n[COMPLETE] {summary}")
                            print(f"[USAGE TOTAL] {state.usage_summary()}")
                            if os.path.exists(state.path):
                                os.remove(state.path)
                            return True

                        # Track HOL session name from hol_start output
                        if "Session '" in text or "session '" in text:
                            # Match: Session 'X' started, Attached to session 'X', etc.
                            match = re.search(r"[Ss]ession '(\w+)'", text)
                            if match and match.group(1) != state.hol_session:
                                state.hol_session = match.group(1)
                                print(f"[HOL] Session: {state.hol_session}")

                    # Check message limit
                    if state.session_message_count >= config.max_agent_messages:
                        print(f"\n[HANDOFF] Reached {config.max_agent_messages} messages...")

                        handoff_prompt = (
                            "STOP. Context clearing - your todo list will NOT persist. "
                            "1) If you made substantial progress, commit it: "
                            "   - NEVER `git add -A` or `git add .` - only specific .sml files "
                            "   - Use `git diff <file>` to verify before adding "
                            "2) Ultrathink like a prompt engineer and write a "
                            f"handoff prompt in {config.task_file} to provide all "
                            "necessary info but context optimized. Tell the next agent to start "
                            "work immediately. Include: "
                            "   - What you tried, what worked "
                            "   - What to try next (be specific - this is your only memory) "
                            "   (goals/holmake are auto-injected at startup)"
                            "3) Leave HOL session running. "
                            "4) STOP after updating task file."
                        )

                        print(f"[SEND] {handoff_prompt}")
                        await client.query(handoff_prompt)
                        async for msg in client.receive_response():
                            print_message_blocks(msg, prefix="  [HANDOFF] ")

                        print(f"[HANDOFF] Agent updated task file")

                        # Clear SDK session to force fresh context, but preserve HOL session
                        state.session_id = None
                        state.session_message_count = 0
                        state.save()
                        print(f"[HANDOFF] Cleared SDK session, {state.message_count} total, HOL '{state.hol_session}'")
                        break

                    # Result message - capture usage and send continue prompt
                    if isinstance(message, ResultMessage):
                        # Capture usage if available
                        print(f"  [RESULT] usage={message.usage}, cost={message.total_cost_usd}")
                        if message.usage:
                            cost = message.total_cost_usd or 0.0
                            state.add_usage(message.usage, cost)
                            print(f"  [USAGE] {state.usage_summary()}")
                            state.save()

                        if message.result:
                            print(f"  [RESULT TEXT] {message.result}")
                        cont = "Continue. PROOF_COMPLETE when holmake passes with no cheats."
                        print(f"[SEND] {cont}")
                        await client.query(cont)

            error_count = 0

        except KeyboardInterrupt:
            state.save()
            print(f"\n[INTERRUPT] State saved")
            print(f"[USAGE TOTAL] {state.usage_summary()}")
            print("  Enter message for Claude, 'q' to quit, empty to continue")
            try:
                user_input = input("\n> ").strip()
                if user_input.lower() == 'q':
                    raise KeyboardInterrupt
                elif user_input:
                    opts = ClaudeAgentOptions(
                        cwd=config.working_dir,
                        model=config.model,
                        system_prompt=system_prompt,
                        allowed_tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob", "mcp__hol__*"],
                disallowed_tools=["TodoRead", "TodoWrite"],
                        mcp_servers=MCP_SERVER_CONFIG,
                        resume=state.session_id,
                        can_use_tool=tool_permission,
                    )
                    async with ClaudeSDKClient(opts) as client:
                        print(f"[SEND] {user_input}")
                        await client.query(user_input)
                        async for msg in client.receive_response():
                            print_message_blocks(msg)
                    continue
                else:
                    continue
            except KeyboardInterrupt:
                print("\n[QUIT]")
                raise

        except Exception as e:
            error_count += 1
            print(f"[ERROR] ({error_count}): {e}")
            import traceback
            traceback.print_exc()

            if error_count >= config.max_consecutive_errors:
                print("[FATAL] Too many errors")
                return False

            await asyncio.sleep(2 ** error_count)


# =============================================================================
# Main
# =============================================================================

def main():
    import argparse

    parser = argparse.ArgumentParser(description="HOL4 Proof Agent")
    parser.add_argument("--task", "-t", required=True, help="Task file (TASK_*.md)")
    parser.add_argument("--claude-md", "-c", help="CLAUDE.md path")
    parser.add_argument("--prompt", "-p", help="Initial prompt")
    parser.add_argument("--fresh", action="store_true", help="Ignore saved session")
    parser.add_argument("--model", "-m", default="claude-opus-4-20250514")
    parser.add_argument("--max-messages", type=int, default=100)

    args = parser.parse_args()

    working_dir = os.getcwd()

    # Find CLAUDE.md
    claude_md = args.claude_md
    if not claude_md:
        for parent in [Path(working_dir)] + list(Path(working_dir).parents):
            candidate = parent / "CLAUDE.md"
            if candidate.exists():
                claude_md = str(candidate)
                break

    config = AgentConfig(
        working_dir=working_dir,
        task_file=os.path.abspath(args.task),
        claude_md=claude_md or "",
        model=args.model,
        max_agent_messages=args.max_messages,
        fresh=args.fresh,
    )

    if args.fresh and os.path.exists(config.state_path):
        os.remove(config.state_path)

    print("=" * 60)
    print("HOL4 Proof Agent (MCP)")
    print("=" * 60)
    print(f"Working dir: {config.working_dir}")
    print(f"Task: {config.task_file}")
    print(f"Model: {config.model}")
    print("=" * 60)

    try:
        success = asyncio.run(run_agent(config, args.prompt))
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\n[PAUSED] Run again to resume")
        sys.exit(2)


if __name__ == "__main__":
    main()
