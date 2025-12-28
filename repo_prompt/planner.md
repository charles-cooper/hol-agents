# Planner Recovery Prompt

## File: `hol_planner.py`

Thin wrapper for Phase 1 (planning). Autonomous mathematical reasoning.

## Purpose

Create rigorous mathematical proof plans with validated assumptions.
Does NOT interact with HOL directly - pure reasoning task.

## CLI Interface

```bash
python hol_planner.py --goal "prove theorem X" [options]

Options:
  --goal, -g    What to prove (required)
  --workdir, -w Working directory (default: cwd)
  --output, -o  Output file for plan
```

## Implementation

```python
async def run_planner(goal: str, workdir: str, output: str = None):
    # 1. Load methodology prompt as system prompt
    system_prompt = read_file("prompts/hol4/planner.md")

    # 2. Configure agent (no MCP needed)
    opts = ClaudeAgentOptions(
        system_prompt=system_prompt,
        allowed_tools=["Read", "Grep", "Glob", "Task", "Write", "Edit"],
        disallowed_tools=["Bash"],  # No shell access
    )

    # 3. Send task
    task = f"""
    Create a rigorous mathematical proof plan for:
    {goal}

    Follow the methodology exactly:
    - Validate ALL assumptions
    - Spawn subagents to check claims
    - ZERO unverified assumptions

    Output PLAN_COMPLETE: when done.
    """
    if output:
        task += f"\nWrite plan to: {output}"

    # 4. Run until PLAN_COMPLETE
    async with ClaudeSDKClient(opts) as client:
        await client.query(task)
        async for message in client.receive_messages():
            if "PLAN_COMPLETE:" in text:
                return True
```

## Key Differences from proof_agent

| Aspect | Planner | Proof Agent |
|--------|---------|-------------|
| MCP | None | Required |
| Forever loop | No | Yes |
| Handoffs | No | Yes |
| State persistence | No | Yes |
| Bash | Disabled | Git only |

## Termination

Runs until:
- Agent outputs "PLAN_COMPLETE:"
- Or interrupted by user

No handoff mechanism - planning should complete in one context.

## Reconstruction Notes

- Much simpler than proof_agent - no MCP, no state, no handoffs
- Uses Task tool for spawning validation subagents
- Bash disabled entirely (pure reasoning)
- Could use Sonnet for cost efficiency (bounded task)
