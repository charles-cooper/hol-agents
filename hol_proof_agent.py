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
   - hol_start(workdir, name) -> Start HOL subprocess with --zero flag
   - hol_sessions() -> List active sessions (name, workdir, age, status)
   - hol_attach(session) -> Attach to existing, return proof state
   - hol_send(session, command, timeout=120) -> Send SML, return output
   - hol_proof_state(session) -> Run p() + top_goals(), return formatted
   - hol_interrupt(session) -> SIGINT to process group
   - hol_stop(session) -> SIGTERM + wait
   - holmake(workdir, target="") -> Run Holmake --qof

   Cursor tools (multi-theorem files):
   - hol_cursor_init(session, file) -> Parse SML, find cheats, load context
   - hol_cursor_status(session) -> Position, completed, remaining cheats
   - hol_cursor_start(session) -> gt `goal`, replay tactics before cheat
   - hol_cursor_complete(session) -> Extract p(), splice into file, advance

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
   - Run hol_proof_state() to capture goals
   - Update task file ## Handoff section with: workdir, branch, hol session name,
     what tried, what worked, current state, next steps
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
   - Recovery: read task file, hol_sessions(), hol_proof_state(), holmake()

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
)


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
    """Build system prompt with task context."""
    claude_md = read_file(config.claude_md)
    task = read_file(config.task_file)
    init = read_file(os.path.join(config.working_dir, ".hol_init.sml"))

    return f"""You are an autonomous HOL4 theorem proving agent. You run FOREVER until the proof is complete.

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
1. `holmake(workdir)` succeeds (set MYVAR if needed for myval builds)
2. NO "CHEAT" warnings in output
3. NO "FAIL" in output

When complete, output "PROOF_COMPLETE:" followed by a summary.

## Working Directory
{config.working_dir}

## CLAUDE.md Guidelines
{claude_md}

## Task
{task}

## .hol_init.sml
{init if init else "(none)"}

## HOL4 MCP Tools

You have access to HOL4 tools via MCP. Use these instead of Bash for HOL interaction:

### Session Management
- `hol_start(workdir, name)` - Start HOL session (idempotent - reuses existing)
- `hol_sessions()` - List all active sessions
- `hol_stop(session)` - Terminate session

### HOL Interaction
- `hol_send(session, command, timeout)` - Send SML code to HOL
- `hol_interrupt(session)` - Abort runaway tactic (SIGINT)
- `holmake(workdir, target)` - Run Holmake --qof

### Cursor Tools (multi-theorem files)
- `hol_cursor_init(session, file)` - Parse file, position at first cheat
- `hol_cursor_status(session)` - Get current position
- `hol_cursor_start(session)` - Enter goaltree mode for current theorem
- `hol_cursor_complete(session)` - Splice proof, advance to next theorem

### Typical Workflow
```
1. hol_start(workdir="/path/to/proofs", name="main")  # Idempotent, returns state
2. hol_send(session="main", command='open fooTheory;')
3. hol_send(session="main", command='gt `goal`;')
4. hol_send(session="main", command='etq "tactic";')
5. holmake(workdir="/path/to/proofs")  # Verify
```

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

1. **Assess**: Run `holmake(workdir)` to see current state
2. **Identify**: Find theorems with CHEAT warnings
3. **Debug interactively**:
   - Start HOL session: `hol_start(workdir, "main")`
   - Send commands: `hol_send("main", 'gt `goal`;')`
   - Try tactics: `hol_send("main", 'etq "tactic";')`
   - Check state: `hol_proof_state("main")`
   - Undo mistakes: `hol_send("main", 'backup();')`
4. **Update file**: Copy tactic script from p() into Theorem block
5. **Verify**: Run holmake again
6. **Iterate**: Until no cheats remain

## Critical Rules

1. NEVER GIVE UP - keep trying different approaches forever
2. If stuck on one approach for 10+ attempts, try a different strategy
3. Helper lemmas are your friend - break big proofs into smaller ones
4. `gvs[AllCaseEqs()]` can be too aggressive - sometimes `fs[]` or `simp[]` is better
5. For induction, make sure IH is applicable (check variable names)
6. If tactic runs >15 seconds, use hol_interrupt and try different approach

## Recovery

If context seems lost:
1. Read task file for ## Handoff section
2. Run hol_start(workdir, name) - idempotent, returns current state
3. Run holmake() to see what's failing

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
                    # Extract result string from MCP response
                    if isinstance(content, dict) and 'result' in content:
                        text = content['result']
                    else:
                        text = content
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

# MCP server configuration
MCP_SERVER_CONFIG = {
    "hol": {
        "command": sys.executable,
        "args": [str(Path(__file__).parent / "hol_mcp_server.py")],
    }
}


async def run_agent(config: AgentConfig, initial_prompt: Optional[str] = None) -> bool:
    """Run the agent until completion."""

    system_prompt = build_system_prompt(config)
    error_count = 0
    message_count = 0
    session_id = None
    state_path = config.state_path
    os.makedirs(os.path.dirname(state_path), exist_ok=True)

    # Load previous state if exists
    session_message_count = 0
    hol_session = None
    if os.path.exists(state_path):
        try:
            with open(state_path) as f:
                state = json.load(f)
                session_id = state.get("session_id")
                message_count = state.get("message_count", 0)
                session_message_count = state.get("session_message_count", 0)
                hol_session = state.get("hol_session")
                if session_id:
                    print(f"[RESUME] Session {session_id} ({session_message_count}/{config.max_agent_messages})")
                if hol_session:
                    print(f"[RESUME] HOL session: {hol_session}")
        except Exception:
            pass

    print(f"[AGENT] Starting (handoff every {config.max_agent_messages} messages)...")

    while True:
        print(f"\n{'='*60}")
        if session_id:
            print(f"[SESSION] Resuming {session_id}")
        elif message_count > 0:
            print(f"[SESSION] New context (continuing from msg {message_count})")
        elif config.fresh:
            print(f"[SESSION] Fresh start")
        else:
            print(f"[SESSION] Starting")
        print(f"{'='*60}")

        try:
            opts = ClaudeAgentOptions(
                cwd=config.working_dir,
                model=config.model,
                system_prompt=system_prompt,
                allowed_tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob", "mcp__hol__*"],
                mcp_servers=MCP_SERVER_CONFIG,
                resume=session_id,
                can_use_tool=tool_permission,
            )

            async with ClaudeSDKClient(opts) as client:
                # Build prompt
                if session_id:
                    prompt = initial_prompt or f"Continue. Task: {config.task_file}"
                    if hol_session:
                        prompt += f" HOL session '{hol_session}' may still be running - use hol_start() to reconnect."
                else:
                    prompt = f"Begin. Read {config.task_file} for ## Handoff section."
                    if initial_prompt:
                        prompt = f"{prompt} Initial instruction: {initial_prompt}"
                    if hol_session:
                        prompt += f" Previous HOL session '{hol_session}' - use hol_start() to reconnect (it's idempotent)."

                    large_files = get_large_files(config.working_dir)
                    if large_files:
                        file_list = ", ".join(f"{f} ({n} lines)" for f, n in large_files[:5])
                        prompt += f" WARNING: Large files: {file_list}"

                await client.query(prompt)

                # Capture session ID
                if hasattr(client, 'session_id') and client.session_id and client.session_id != session_id:
                    session_id = client.session_id
                    print(f"[SESSION] Got ID: {session_id}")

                # Process messages
                async for message in client.receive_messages():
                    msg_type = type(message).__name__

                    # Capture session_id
                    if hasattr(message, 'session_id') and message.session_id:
                        if session_id != message.session_id:
                            session_id = message.session_id
                            print(f"[SESSION] Got ID: {session_id}")

                    # Count assistant messages
                    if msg_type == "AssistantMessage":
                        session_message_count += 1
                        message_count += 1
                        print(f"[MSG {session_message_count}/{config.max_agent_messages}] (total: {message_count})")

                        # Save state
                        with open(state_path, 'w') as f:
                            json.dump({
                                "session_id": session_id,
                                "message_count": message_count,
                                "session_message_count": session_message_count,
                                "hol_session": hol_session,
                            }, f)

                    # Log and check for completion
                    texts = print_message_blocks(message)
                    for text in texts:
                        if "PROOF_COMPLETE:" in text:
                            summary = text.split("PROOF_COMPLETE:")[-1].strip()
                            print(f"\n[COMPLETE] {summary}")
                            if os.path.exists(state_path):
                                os.remove(state_path)
                            return True

                        # Track HOL session name from hol_start or hol_attach output
                        if "Session '" in text or "session '" in text:
                            # Match: Session 'X' started, Attached to session 'X', etc.
                            match = re.search(r"[Ss]ession '(\w+)'", text)
                            if match and match.group(1) != hol_session:
                                hol_session = match.group(1)
                                print(f"[HOL] Session: {hol_session}")

                    # Check message limit
                    if session_message_count >= config.max_agent_messages:
                        print(f"\n[HANDOFF] Reached {config.max_agent_messages} messages...")

                        handoff_prompt = (
                            "STOP. Context clearing now. "
                            "1) Commit progress if substantial (git add specific files only, never -A). "
                            "2) Update task file with ## Handoff section: "
                            "   - Working directory, git branch, HOL session name "
                            "   - What you tried, what worked "
                            "   - What to try next "
                            "3) DO NOT stop the HOL session - leave it running. "
                            "4) STOP after updating task file."
                        )

                        await client.query(handoff_prompt)
                        async for msg in client.receive_response():
                            print_message_blocks(msg, prefix="  [HANDOFF] ")

                        # Clear session for new start
                        session_id = None
                        session_message_count = 0
                        with open(state_path, 'w') as f:
                            json.dump({
                                "session_id": None,
                                "message_count": message_count,
                                "session_message_count": 0,
                                "hol_session": hol_session,
                            }, f)
                        print(f"[HANDOFF] Cleared session, HOL '{hol_session}' preserved")
                        break

                    # Result message - send continue prompt
                    if hasattr(message, 'result'):
                        result = message.result or ""
                        if result:
                            print(f"  [RESULT] {result}")
                        await client.query("Continue. Output PROOF_COMPLETE: <summary> when done.")

            error_count = 0

        except KeyboardInterrupt:
            with open(state_path, 'w') as f:
                json.dump({
                    "session_id": session_id,
                    "message_count": message_count,
                    "session_message_count": session_message_count,
                    "hol_session": hol_session,
                }, f)
            print(f"\n[INTERRUPT] State saved")
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
                        mcp_servers=MCP_SERVER_CONFIG,
                        resume=session_id,
                        can_use_tool=tool_permission,
                    )
                    async with ClaudeSDKClient(opts) as client:
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
