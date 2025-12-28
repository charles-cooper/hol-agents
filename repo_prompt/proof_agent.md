# Proof Agent Recovery Prompt

## File: `hol_proof_agent.py`

Full orchestrator for Phase 3 (proving). Runs forever until PROOF_COMPLETE.

## Dependencies

- claude-agent-sdk >= 0.1.0
- hol_mcp_server.py (imported for MCP instance)

## CLI Interface

```bash
python hol_proof_agent.py --task TASK_foo.md [options]

Options:
  --task, -t      Task file (required)
  --claude-md, -c CLAUDE.md path
  --prompt, -p    Initial prompt override
  --fresh         Ignore saved session state
  --model, -m     Model name (default: claude-sonnet-4-...)
  --max-messages  Messages before handoff (default: 100)
```

## State Persistence

```python
# .claude/hol_agent_state.json
{
    "session_id": str,           # Claude SDK session ID (for resume)
    "message_count": int,        # Total messages across all handoffs
    "session_message_count": int,# Messages in current session
    "hol_session": str,          # HOL session name (key into MCP registry)
    "holmake_env": dict,         # Cached env vars for holmake
    "input_tokens": int,         # Usage tracking
    "output_tokens": int,
    "cache_creation_tokens": int,
    "cache_read_tokens": int,
    "total_cost_usd": float
}
```

## Main Loop

```python
async def run_agent(config):
    while True:
        # 1. Load or create state
        state = AgentState.load(config.state_path)

        # 2. Build system prompt from template
        system_prompt = build_system_prompt(config)

        # 3. Create SDK client with MCP
        opts = ClaudeAgentOptions(
            system_prompt=system_prompt,
            mcp_servers={"hol": hol_mcp_instance},
            resume=state.session_id,  # Resume if exists
            allowed_tools=[..., "mcp__hol__*"],
        )

        async with ClaudeSDKClient(opts) as client:
            # 4. Send initial prompt
            if state.session_id:
                prompt = "Continue."
            else:
                prompt = build_initial_prompt(config, state)

            await client.query(prompt)

            # 5. Process messages
            async for message in client.receive_messages():
                # Count assistant messages
                # Save state after each
                # Check for PROOF_COMPLETE:
                # Trigger handoff at max_messages
```

## Handoff Protocol

At max_messages, before context clear:

```python
handoff_prompt = """
STOP. Context clearing.
1) Commit progress (git add specific files, never -A)
2) Update task file ## Handoff section:
   - What tried, what worked
   - What to try next (specific)
   (goals/holmake auto-injected at startup)
3) Leave HOL session running
4) STOP after updating task file
"""
```

After handoff:
- Clear session_id (forces new Claude context)
- Preserve hol_session (HOL keeps running in MCP server)
- Loop back to start

## Initial Prompt Construction

For new sessions (not resume):

```python
prompt = f"""
## Task File: {config.task_file}
{task_content}

## .hol_init.sml
{init_content}

Begin. Check ## Handoff section for current state.
Previous HOL session: '{state.hol_session}'.

[auto] hol_sessions(): ...
[auto] top_goals(): ...
[auto] holmake(): ...
"""
```

Auto-injected state saves agent turns.

## Bash Restriction

```python
ALLOWED_GIT_SUBCOMMANDS = {"add", "commit", "status", "diff", "log", ...}

def is_allowed_command(cmd):
    # Only git commands allowed
    # Reject shell operators (;, |, &, etc.)
    # All HOL via MCP tools
```

## System Prompt Template

Located at: `prompts/hol4/proof_agent.template.md`

Template variables:
- `{max_agent_messages}` - Handoff threshold
- `{claude_md}` - CLAUDE.md content
- `{mcp}` - MCP tool prefix ("mcp__hol__")

## Key Invariants

1. **HOL sessions survive handoffs** - MCP server keeps them alive
2. **SDK sessions don't survive handoffs** - Context cleared, new session
3. **State file bridges handoffs** - Preserves hol_session name
4. **Agent runs forever** - Until PROOF_COMPLETE detected
5. **All HOL via MCP** - Bash restricted to git only

## Interrupt Handling

Ctrl+C:
1. Save state
2. Prompt user for input
3. 'q' to quit, message to send, empty to continue

## Reconstruction Notes

- MCP server must be imported (not spawned) for session persistence
- Use `type: "sdk"` in mcp_servers config to share instance
- Resume requires session_id from previous run
- Handoff preserves HOL session name, not SDK session
- Usage tracking optional but useful for cost monitoring
