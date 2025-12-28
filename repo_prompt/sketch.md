# Sketch Recovery Prompt

## File: `hol_sketch.py`

Thin wrapper for Phase 2 (sketching). Translates plans to HOL4 code structure.

## Purpose

Create HOL4 SML files with cheats + task files for subagents.
Uses MCP for holmake verification.

## CLI Interface

```bash
python hol_sketch.py --plan plan.md --workdir /path [options]

Options:
  --plan, -p      Plan file to implement (required)
  --workdir, -w   Working directory (default: cwd)
  --output-dir, -o Output directory for sketch files
```

## Implementation

```python
async def run_sketch(plan_file: str, workdir: str, output_dir: str = None):
    # 1. Load methodology prompt as system prompt
    system_prompt = read_file("prompts/hol4/sketch_impl.md")

    # 2. Load plan content
    plan_content = read_file(plan_file)

    # 3. Configure agent (MCP for holmake)
    opts = ClaudeAgentOptions(
        system_prompt=system_prompt,
        mcp_servers={"hol": hol_mcp_instance},
        allowed_tools=["Read", "Write", "Edit", "Grep", "Glob", "Task", "mcp__hol__*"],
        disallowed_tools=["Bash"],
    )

    # 4. Send task
    task = f"""
    Create HOL4 proof sketch from this plan:
    {plan_content}

    Follow methodology:
    - Split into subtasks if needed
    - SML must COMPILE (verify with holmake)
    - Every theorem needs WHY THIS IS TRUE
    - Create TASK_*.md for each cheat

    Output SKETCH_COMPLETE: when done.
    """

    # 5. Run until SKETCH_COMPLETE
    async with ClaudeSDKClient(opts) as client:
        await client.query(task)
        async for message in client.receive_messages():
            if "SKETCH_COMPLETE:" in text:
                return True
```

## Outputs

```
workdir/
├── *_sketch.sml     # Compilable HOL4 with cheats
└── TASK_*.md        # One per cheat

# Task file format:
# TASK: theorem_name - description
## Goal
## Theorem Statement
## Mathematical Argument (WHY THIS IS TRUE)
## Available Resources
## Proof Approach
## Constraints
## Deliverable
```

## Key Differences from proof_agent

| Aspect | Sketch | Proof Agent |
|--------|--------|-------------|
| MCP | holmake only | Full session |
| Forever loop | No | Yes |
| Handoffs | No | Yes |
| HOL session | No | Yes |

## Termination

Runs until:
- Agent outputs "SKETCH_COMPLETE:"
- Or interrupted by user

Should complete in one context (split subtasks if too large).

## Reconstruction Notes

- Needs MCP for holmake compilation verification
- Does NOT need persistent HOL session (just build checks)
- Simpler than proof_agent - no handoffs, no state
- Output includes both .sml files and .md task files
- Could use Sonnet for cost efficiency
