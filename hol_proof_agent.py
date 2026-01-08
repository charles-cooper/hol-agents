#!/usr/bin/env python3
"""HOL4 Proof Agent - Phase 3 orchestrator. See repo_prompt/ for recovery prompts."""

import asyncio
import glob
import json
import os
import re
import shlex
import sys
from pathlib import Path
from dataclasses import asdict, dataclass
from datetime import datetime
from typing import Optional

from claude_agent_sdk import (
    ClaudeAgentOptions,
    ClaudeSDKClient,
    PermissionResultAllow,
    PermissionResultDeny,
    ResultMessage,
)
from claude_agent_sdk.types import StreamEvent

# Import MCP server instance - allows HOL sessions to persist across handoffs
from hol_mcp_server import mcp as hol_mcp, _sessions, hol_sessions, hol_send, holmake, set_agent_state


_log_fh = None
_log_path = None
MAX_LOG_SIZE = 75 * 1024 * 1024  # 75 MB


def setup_logging(working_dir: str):
    global _log_fh, _log_path
    log_dir = os.path.join(working_dir, ".claude", "logs")
    os.makedirs(log_dir, exist_ok=True)
    _log_path = os.path.join(log_dir, "hol_agent_debug.log")
    _log_fh = open(_log_path, 'a', buffering=1)


def _rotate_log():
    global _log_fh
    _log_fh.close()
    backup = _log_path + '.old'
    if os.path.exists(backup):
        os.remove(backup)
    os.rename(_log_path, backup)
    _log_fh = open(_log_path, 'w', buffering=1)


def log(msg: str):
    if _log_fh:
        print(f"{datetime.now():%H:%M:%S} {msg}", file=_log_fh)
        if _log_fh.tell() > MAX_LOG_SIZE:
            _rotate_log()


def log_message(message):
    log(f"{type(message).__name__}: {json.dumps(asdict(message), default=str)}")


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
    scratch_file: str  # Working state, handoff notes (separate from task intent)
    claude_md: str
    model: str = "claude-opus-4-5-20251101"
    max_consecutive_errors: int = 5
    max_agent_messages: int = 100
    max_context_tokens: int = 100000  # Handoff when context size exceeds this (half of 200k)
    max_thinking_tokens: int = 31999  # Extended thinking budget (ultrathink default)
    fresh: bool = False
    enable_logging: bool = True

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

    def save(self) -> None:
        with open(self.path, 'w') as f:
            json.dump({
                "session_id": self.session_id,
                "message_count": self.message_count,
                "session_message_count": self.session_message_count,
                "hol_session": self.hol_session,
                "holmake_env": self.holmake_env,
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


def derive_scratch_file(task_file: str) -> str:
    """Derive scratch file path from task file: TASK_foo.md / PROMPT_foo.md -> SCRATCH_foo.md"""
    dirname = os.path.dirname(task_file)
    basename = os.path.basename(task_file)
    for prefix in ("TASK_", "PROMPT_"):
        if basename.startswith(prefix):
            scratch_name = "SCRATCH_" + basename[len(prefix):]
            break
    else:
        scratch_name = "SCRATCH_" + basename
    return os.path.join(dirname, scratch_name)


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
    """Build static system prompt from template file."""
    # Find template relative to this script
    script_dir = Path(__file__).parent
    template_path = script_dir / "prompts" / "hol4" / "proof_agent.template.md"
    template = read_file(str(template_path))

    if not template:
        raise RuntimeError(f"Failed to load system prompt template: {template_path}")

    claude_md = read_file(config.claude_md)

    return template.format(
        max_agent_messages=config.max_agent_messages,
        claude_md=claude_md,
        mcp="mcp__hol__",
    )


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
    if config.enable_logging:
        setup_logging(config.working_dir)
        log(f"=== Agent started: {config.task_file} ===")

    system_prompt = build_system_prompt(config)
    error_count = 0
    os.makedirs(os.path.dirname(config.state_path), exist_ok=True)

    # Load previous state
    state = AgentState.load(config.state_path)
    set_agent_state(state)  # Enable direct holmake_env capture

    print(f"[AGENT] Starting (handoff at {config.max_context_tokens:,} tokens or {config.max_agent_messages} messages)...")

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
                max_thinking_tokens=config.max_thinking_tokens,
                include_partial_messages=True,  # Get StreamEvents for per-turn token tracking
            )

            async with ClaudeSDKClient(opts) as client:
                # Build prompt
                if state.session_id:
                    # Resuming SDK session - agent has context
                    prompt = initial_prompt or "Continue."
                else:
                    # New SDK session - include task file, scratch file, and context
                    task = read_file(config.task_file)
                    scratch = read_file(config.scratch_file)
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
                            hol_state += f"Remaining cheats: {len(status['cheats'])}"
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
                    if scratch:
                        prompt += f"## Scratch File: {config.scratch_file}\n{scratch}\n\n"
                    if init:
                        prompt += f"## .hol_init.sml\n{init}\n\n"

                    prompt += "Begin."
                    if scratch:
                        prompt += " Check scratch file for previous handoff state."
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

                # Track context tokens from StreamEvents
                context_tokens = 0

                # Process messages
                async for message in client.receive_messages():
                    msg_type = type(message).__name__
                    log_message(message)

                    # Extract context size from StreamEvent message_start
                    if isinstance(message, StreamEvent):
                        event = message.event
                        if event.get("type") == "message_start":
                            usage = event.get("message", {}).get("usage", {})
                            input_tokens = usage.get("input_tokens", 0)
                            cache_read = usage.get("cache_read_input_tokens", 0)
                            cache_create = usage.get("cache_creation_input_tokens", 0)
                            context_tokens = input_tokens + cache_read + cache_create
                        continue  # Don't process StreamEvents further

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
                        print(f"[MSG {state.session_message_count}/{config.max_agent_messages}] [CTX {context_tokens:,}]")
                        # Sync holmake_env from session entry
                        if state.hol_session and state.hol_session in _sessions:
                            entry_env = _sessions[state.hol_session].holmake_env
                            if entry_env != state.holmake_env:
                                state.holmake_env = entry_env
                        state.save()

                    # Log and check for completion
                    texts = print_message_blocks(message)
                    for text in texts:
                        if text.startswith("[PROOF_COMPLETE]"):
                            print(f"\n[COMPLETE]")
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

                    # Check message limit or context token limit
                    handoff_reason = None
                    if context_tokens >= config.max_context_tokens:
                        handoff_reason = f"Context size {context_tokens:,} >= {config.max_context_tokens:,} tokens"
                    elif state.session_message_count >= config.max_agent_messages:
                        handoff_reason = f"Reached {config.max_agent_messages} messages"

                    if handoff_reason:
                        print(f"\n[HANDOFF] {handoff_reason}...")

                        handoff_prompt = (
                            "STOP. Context clearing - your todo list will NOT persist. "
                            "1) If you made substantial progress, commit it: "
                            "   - NEVER `git add -A` or `git add .` - only specific .sml files "
                            "   - Use `git diff <file>` to verify before adding "
                            "2) Ultrathink like a prompt engineer and write handoff notes to "
                            f"{config.scratch_file} (NOT the task file). Include: "
                            "   - What you tried, what worked "
                            "   - What to try next (be specific - this is your only memory) "
                            "   (goals/holmake are auto-injected at startup) "
                            "3) Leave HOL session running. "
                            "4) STOP after updating scratch file."
                        )

                        print(f"[SEND] {handoff_prompt}")
                        await client.query(handoff_prompt)
                        async for msg in client.receive_response():
                            print_message_blocks(msg, prefix="  [HANDOFF] ")

                        print(f"[HANDOFF] Agent updated scratch file")

                        # Clear SDK session to force fresh context, but preserve HOL session
                        state.session_id = None
                        state.session_message_count = 0
                        state.save()
                        print(f"[HANDOFF] Cleared SDK session, {state.message_count} total, HOL '{state.hol_session}'")
                        break

                    # Result message - send continue prompt
                    if isinstance(message, ResultMessage):
                        if message.result:
                            print(f"  [RESULT TEXT] {message.result}")
                        cont = "Continue. Start your message with [PROOF_COMPLETE] when done."
                        print(f"[SEND] {cont}")
                        await client.query(cont)

            error_count = 0

        except KeyboardInterrupt:
            state.save()
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
                        disallowed_tools=["TodoRead", "TodoWrite"],
                        mcp_servers=MCP_SERVER_CONFIG,
                        resume=state.session_id,
                        can_use_tool=tool_permission,
                        max_thinking_tokens=config.max_thinking_tokens,
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
    parser.add_argument("--model", "-m", default="claude-opus-4-5-20251101")
    parser.add_argument("--max-messages", type=int, default=100, help="Handoff after N messages")
    parser.add_argument("--max-context-tokens", type=int, default=100000, help="Handoff when context exceeds N tokens (default 100k = half of 200k window)")
    parser.add_argument("--thinking-tokens", type=int, default=31999, help="Extended thinking budget (ultrathink=31999)")
    parser.add_argument("--no-log", action="store_true", help="Disable debug logging to file")

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

    task_file = os.path.abspath(args.task)
    config = AgentConfig(
        working_dir=working_dir,
        task_file=task_file,
        scratch_file=derive_scratch_file(task_file),
        claude_md=claude_md or "",
        model=args.model,
        max_agent_messages=args.max_messages,
        max_context_tokens=args.max_context_tokens,
        max_thinking_tokens=args.thinking_tokens,
        fresh=args.fresh,
        enable_logging=not args.no_log,
    )

    if args.fresh and os.path.exists(config.state_path):
        os.remove(config.state_path)

    print("=" * 60)
    print("HOL4 Proof Agent (MCP)")
    print("=" * 60)
    print(f"Working dir: {config.working_dir}")
    print(f"Task: {config.task_file}")
    print(f"Scratch: {config.scratch_file}")
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
