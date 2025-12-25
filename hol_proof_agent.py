#!/usr/bin/env python3
"""
HOL4 Proof Development Agent

Implement an autonomous agent using the Claude Agent SDK (claude-agent-sdk) that:

1. AUTHENTICATION
   - Uses Claude Agent SDK which spawns Claude Code CLI as subprocess
   - OAuth handled automatically via ~/.claude/.credentials.json (Max subscription)
   - No API key needed - uses Claude Code's auth

2. TOOL RESTRICTIONS
   - Implement can_use_tool callback to restrict available tools
   - Allow: Read, Write, Edit, Grep, Glob
   - Allow Bash ONLY for: Holmake, hol-agent-helper.sh commands
   - Deny all other Bash commands (return PermissionResultDeny)

3. SESSION MANAGEMENT
   - Save session_id to .agent_state.json for resume (like `claude -r`)
   - On restart, load session_id and pass to ClaudeAgentOptions(resume=session_id)
   - Track total_messages across sessions

4. CONTEXT MANAGEMENT (handoff every N messages)
   - Count AssistantMessage instances
   - After max_agent_messages (default 40), trigger handoff:
     a) Ask Claude to commit progress if substantial
     b) Ask Claude to run p() and include proof state
     c) Ask Claude to update task file with ## Handoff section
     d) Clear session_id (force new session)
   - On resume without session_id, task file contains handoff context

5. INTERRUPT HANDLING (Ctrl+C)
   - First Ctrl+C: prompt for user input
     - User can send message to Claude (resumes session)
     - Empty input: continue
     - 'q' or second Ctrl+C: save state and quit
   - Save session_id to state file on quit

6. COMPLETION
   - Watch for "PROOF_COMPLETE:" in Claude's text output
   - Clean up state files on completion
   - Exit with success

7. OBSERVABILITY
   - Print [MSG n/max] (total: N) for each assistant message
   - Print [TOOL] name: {input} for tool calls
   - Print [TEXT] for text blocks
   - Print [SESSION] when getting/resuming session ID
   - Print [HANDOFF] during context clearing

8. CLI INTERFACE
   - --task/-t: Task file path (required)
   - --claude-md/-c: CLAUDE.md path (auto-discovered if not provided)
   - --prompt/-p: Initial prompt
   - --fresh: Clear state file (but keep handoff)
   - --model/-m: Model to use
   - --max-messages: Messages before handoff (default 40)

9. SYSTEM PROMPT
   - Include CLAUDE.md content
   - Include task file content
   - Include .hol_init.sml if present
   - Document hol-agent-helper.sh commands
   - Instruct completion criteria (Holmake passes, no CHEAT warnings)
"""

import asyncio
import json
import os
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
from datetime import datetime

from claude_agent_sdk import query, ClaudeAgentOptions, ClaudeSDKClient, PermissionResultAllow, PermissionResultDeny

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
    max_agent_messages: int = 40  # Clear context after this many agent messages


def read_file(path: str) -> str:
    """Read a file, return empty string on error."""
    try:
        with open(path, 'r') as f:
            return f.read()
    except:
        return ""


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

**Before proving:** Understand *why* it's true. Write a 2-3 sentence proof sketch.
If you can't explain the argument, you can't guide tactics effectively.

**Performance:** Be mindful of proof performance:
- If a tactic takes >15 seconds, use `interrupt` command - do NOT wait
- `metis_tac` on large search space hangs - avoid or constrain
- `fs[recursive_def]` causes blowup - use `simp[Once def]` instead
- Test tactics individually before combining

## COMPLETION CRITERIA
The proof is complete when:
1. `VFMDIR=/home/ubuntu/verifereum Holmake --qof` succeeds (exit 0)
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

## HOL4 Interactive Session Commands

Use the Bash tool with ~/hol-agents/hol-agent-helper.sh:

```bash
# Start session
~/hol-agents/hol-agent-helper.sh start

# Check status
~/hol-agents/hol-agent-helper.sh status

# Send command (no backquotes)
~/hol-agents/hol-agent-helper.sh send 'open fooTheory;'

# For backquoted terms, write to .hol_cmd.sml first, then:
~/hol-agents/hol-agent-helper.sh send:.hol_cmd.sml

# Interrupt runaway commands
~/hol-agents/hol-agent-helper.sh interrupt

# Stop session
~/hol-agents/hol-agent-helper.sh stop
```

## Goaltree Mode (Interactive Proving)

Always use goaltree mode (`gt`/`etq`) - it records tactics for extraction:

| Command | Purpose |
|---------|---------|
| `gt `tm`` | Start proof (goaltree mode) |
| `etq "tac"` | Apply tactic (records as string for extraction) |
| `p()` | Show proof tree - copy directly to Theorem block |
| `b()` / `backup()` | Undo last tactic |
| `top_goals()` | List remaining goals |
| `drop()` | Abandon proof |

## Subgoal Patterns

- `'tm' by tac` - prove tm, add as assumption (tac must close it)
- `sg 'tm' >- tac` - tm as subgoal, tac must close it
- `'tm' suffices_by tac` - prove tm => goal

## Theorem Search

`DB.find "name"` | `DB.match [] ``pat``` | `DB.theorems "thy"`

## Workflow

1. **Assess**: Run `VFMDIR=/home/ubuntu/verifereum Holmake --qof` to see current state
2. **Identify**: Find theorems with CHEAT warnings
3. **Debug interactively**:
   - Start HOL session
   - Write goal to .hol_cmd.sml: `gt `goal`;`
   - Send it: `~/hol-agents/hol-agent-helper.sh send:.hol_cmd.sml`
   - Check log: `~/hol-agents/hol-agent-helper.sh log`
   - Try tactics via etq: `etq "tactic";`
   - Use `p()` to see proof tree - output is copy-paste ready
   - Use `backup()` to undo mistakes
4. **Update file**: Copy tactic script from `p()` into Theorem block
5. **Verify**: Run Holmake again
6. **Iterate**: Until no cheats remain

## Critical Rules

1. NEVER GIVE UP - keep trying different approaches forever
2. After EVERY hol-agent-helper.sh send, run log to see output
3. If stuck on one approach for 10+ attempts, try a completely different strategy
4. Helper lemmas are your friend - break big proofs into smaller ones that fit in context
5. `gvs[AllCaseEqs()]` can be too aggressive - sometimes `fs[]` or `simp[]` is better
6. For induction, make sure IH is applicable (check variable names)
7. If tactic runs >15 seconds, interrupt and try a different approach

## Recovery

If context seems lost:
1. Read task file
2. Run hol-agent-helper.sh status
3. If session running, send `p();` and check log
4. Run Holmake to see what's failing

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
                    content = content if isinstance(content, str) else str(content)
                    print(f"{prefix}[TOOL OUTPUT] {content}")
                else:
                    print(f"{prefix}[TOOL OUTPUT] (none)")
            elif hasattr(block, 'text') and block.text:
                texts.append(block.text)
                print(f"{prefix}[TEXT] {block.text}")
    return texts


# =============================================================================
# Tool Permission Callback
# =============================================================================

ALLOWED_BASH_PATTERNS = [
    "Holmake",
    "VFMDIR=/home/ubuntu/verifereum Holmake",
    "~/hol-agents/hol-agent-helper.sh",
    "/home/ubuntu/hol-agents/hol-agent-helper.sh",
]


async def hol_tool_permission(tool_name, tool_input, context):
    """Allow only HOL-related tools. SDK requires async signature."""
    if tool_name in ["Read", "Write", "Edit", "Grep", "Glob"]:
        return PermissionResultAllow()

    if tool_name == "Bash":
        command = tool_input.get("command", "")
        for pattern in ALLOWED_BASH_PATTERNS:
            if command.startswith(pattern):
                return PermissionResultAllow()
        return PermissionResultDeny(message="Only Holmake and hol-agent-helper.sh allowed")

    return PermissionResultDeny(message=f"Tool {tool_name} not allowed")


# =============================================================================
# Agent
# =============================================================================

async def run_agent(config: AgentConfig, initial_prompt: Optional[str] = None) -> bool:
    """Run the agent until completion."""

    system_prompt = build_system_prompt(config)
    error_count = 0
    message_count = 0
    session_id = None
    state_path = os.path.join(config.working_dir, ".agent_state.json")

    # Load previous state if exists
    if os.path.exists(state_path):
        try:
            with open(state_path) as f:
                state = json.load(f)
                session_id = state.get("session_id")
                message_count = state.get("message_count", 0)
                if session_id:
                    print(f"[RESUME] Found session {session_id} ({message_count} messages)")
        except:
            pass

    print(f"[AGENT] Starting (handoff every {config.max_agent_messages} agent messages)...")

    while True:
        session_message_count = 0
        print(f"\n{'='*60}")
        if session_id:
            print(f"[SESSION] Resuming {session_id}")
        else:
            print(f"[SESSION] Starting new session")
        print(f"{'='*60}")

        try:
            # Set resume option if we have a session
            opts = ClaudeAgentOptions(
                cwd=config.working_dir,
                model=config.model,
                system_prompt=system_prompt,
                allowed_tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
                can_use_tool=hol_tool_permission,
                resume=session_id,
            )

            async with ClaudeSDKClient(opts) as client:
                # Build and send prompt
                if session_id:
                    # Resuming session - just continue
                    prompt = "Continue."
                else:
                    # Fresh start or after handoff (handoff is in task file's ## Handoff section)
                    prompt = initial_prompt or "Begin. Check the task file for any ## Handoff section from previous sessions."

                await client.query(prompt)

                # Check if client has session_id after query
                if hasattr(client, 'session_id') and client.session_id and client.session_id != session_id:
                    session_id = client.session_id
                    print(f"[SESSION] Got ID from client: {session_id}")
                    with open(state_path, 'w') as f:
                        json.dump({"session_id": session_id, "message_count": message_count}, f)

                # Process messages until we hit the limit
                async for message in client.receive_messages():
                    msg_type = type(message).__name__

                    # Capture session_id - check multiple sources
                    new_session_id = None
                    if hasattr(message, 'session_id') and message.session_id:
                        new_session_id = message.session_id
                    elif msg_type == "SystemMessage" and hasattr(message, 'data') and isinstance(message.data, dict):
                        new_session_id = message.data.get('session_id')

                    if new_session_id and session_id != new_session_id:
                        session_id = new_session_id
                        print(f"[SESSION] Got ID: {session_id}")
                        # Save immediately so we can resume if interrupted
                        with open(state_path, 'w') as f:
                            json.dump({"session_id": session_id, "message_count": message_count}, f)

                    # Count assistant messages
                    if msg_type == "AssistantMessage":
                        session_message_count += 1
                        message_count += 1
                        print(f"[MSG {session_message_count}/{config.max_agent_messages}] (total: {message_count})")
                        # Save state after each message
                        with open(state_path, 'w') as f:
                            json.dump({"session_id": session_id, "message_count": message_count}, f)

                    # Log content and check for completion
                    texts = print_message_blocks(message)
                    for text in texts:
                        if "PROOF_COMPLETE:" in text:
                            summary = text.split("PROOF_COMPLETE:")[-1].strip()
                            print(f"\n[COMPLETE] {summary}")
                            # Clean up state file
                            if os.path.exists(state_path):
                                os.remove(state_path)
                            return True

                    # Check if we hit the message limit
                    if session_message_count >= config.max_agent_messages:
                        print(f"\n[HANDOFF] Reached {config.max_agent_messages} agent messages, stopping session...")

                        # Ask for handoff summary and commit
                        await client.query(
                            "STOP. We're clearing context now. "
                            "1) If you made substantial progress (cleared a cheat, restructured proof), commit it: "
                            "   - NEVER use `git add -A` or `git add .` - add specific files only "
                            "   - Run `git status` first to check what you're committing "
                            "   - Don't commit temp files, credentials, or .agent_* files "
                            "2) If HOL session is running, run p() and get the proof state. "
                            "3) Update the task file: add or replace a `## Handoff` section at the end with: "
                            "   - What you tried and what worked "
                            "   - Current proof state (p() output) "
                            "   - What to try next "
                            "4) DO NOT stop the HOL session - leave it running. "
                            "5) After updating the task file, STOP. Do not continue working.")

                        # Wait for agent to finish handoff
                        async for msg in client.receive_response():
                            print_message_blocks(msg, prefix="  [HANDOFF] ")

                        print(f"[HANDOFF] Agent updated task file")

                        # Clear session_id to force new session after handoff
                        session_id = None
                        with open(state_path, 'w') as f:
                            json.dump({"session_id": None, "message_count": message_count}, f)
                        print(f"[HANDOFF] Cleared session, {message_count} total messages")

                        print("[HANDOFF] Breaking out of session...")
                        break

                    # Result message ends this response
                    if hasattr(message, 'result'):
                        result = message.result or ""
                        if result:
                            print(f"  [RESULT] {result}")
                        # Send continue prompt
                        await client.query("Continue working. Do not stop until Holmake passes with no cheats. Output PROOF_COMPLETE: <summary> when done.")

            error_count = 0

        except KeyboardInterrupt:
            # Save state immediately on interrupt
            with open(state_path, 'w') as f:
                json.dump({"session_id": session_id, "message_count": message_count}, f)
            print(f"\n[INTERRUPT] State saved (session {session_id or 'None'}, {message_count} messages)")
            print("  Enter message to send to Claude")
            print("  'q' or Ctrl+C again to quit")
            print("  Empty to continue")
            try:
                user_input = input("\n> ").strip()
                if user_input.lower() == 'q':
                    raise KeyboardInterrupt
                elif user_input:
                    # Send user message in new session with current context
                    user_opts = ClaudeAgentOptions(
                        cwd=config.working_dir,
                        model=config.model,
                        system_prompt=system_prompt,
                        allowed_tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
                        can_use_tool=hol_tool_permission,
                        resume=session_id,
                    )
                    async with ClaudeSDKClient(user_opts) as client:
                        await client.query(user_input)
                        async for message in client.receive_response():
                            print_message_blocks(message)
                    # Continue with next session
                    continue
                else:
                    # Empty input - continue
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
                print("[FATAL] Too many consecutive errors")
                return False

            await asyncio.sleep(2 ** error_count)


# =============================================================================
# Main
# =============================================================================

def main():
    import argparse

    parser = argparse.ArgumentParser(description="HOL4 Proof Agent - runs until completion")
    parser.add_argument("--task", "-t", required=True, help="Task file (TASK_*.md)")
    parser.add_argument("--claude-md", "-c", help="CLAUDE.md path")
    parser.add_argument("--prompt", "-p", help="Initial prompt")
    parser.add_argument("--fresh", action="store_true", help="Ignore saved session")
    parser.add_argument("--model", "-m", default="claude-opus-4-20250514", help="Model to use")
    parser.add_argument("--max-messages", type=int, default=40, help="Agent messages before handoff (default: 40)")

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
    )

    # Clear state (but not handoff) if fresh start requested
    state_file = os.path.join(working_dir, ".agent_state.json")
    if args.fresh and os.path.exists(state_file):
        os.remove(state_file)

    print("=" * 60)
    print("HOL4 Proof Agent (Claude Agent SDK)")
    print("=" * 60)
    print(f"Working dir: {config.working_dir}")
    print(f"Task: {config.task_file}")
    print(f"Model: {config.model}")
    print("=" * 60)
    print("Running until completion (Ctrl+C to pause)")
    print()

    try:
        success = asyncio.run(run_agent(config, args.prompt))
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\n[PAUSED] Run again to resume")
        sys.exit(2)


if __name__ == "__main__":
    main()
