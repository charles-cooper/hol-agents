# Pipeline Recovery Prompt

## File: `hol_pipeline.py`

End-to-end automation: Plan → Sketch → Prove.

## CLI Interface

```bash
python hol_pipeline.py --theorem "name" --workdir /path [options]

Options:
  --theorem, -t   Theorem to prove (required)
  --workdir, -w   Working directory (default: cwd)
  --skip-plan     Skip planning phase
  --skip-sketch   Skip sketching phase
  --plan, -p      Use existing plan file
```

## Implementation

```python
async def run_pipeline(theorem: str, workdir: str, skip_plan=False, skip_sketch=False):
    output_dir = f"{workdir}/.hol_pipeline"
    plan_path = f"{output_dir}/plan_{theorem}.md"
    sketch_dir = f"{output_dir}/sketches"

    # Phase 1: Planning
    if not skip_plan:
        success = await run_planner(
            goal=f"Prove theorem: {theorem}",
            workdir=workdir,
            output=plan_path,
        )
        if not success:
            return False

    # Phase 2: Sketching
    if not skip_sketch:
        success = await run_sketch(
            plan_file=plan_path,
            workdir=workdir,
            output_dir=sketch_dir,
        )
        if not success:
            return False

    # Phase 3: Proving (each task file)
    task_files = glob.glob(f"{sketch_dir}/TASK_*.md")

    for task_file in task_files:
        config = AgentConfig(
            working_dir=workdir,
            task_file=task_file,
            max_agent_messages=50,  # Smaller for pipeline
        )
        success = await run_agent(config)
        if not success:
            return False

    return True
```

## Output Structure

```
workdir/.hol_pipeline/
├── plan_theorem.md          # Phase 1 output
└── sketches/
    ├── theorem_sketch.sml   # Phase 2 output
    ├── TASK_foo.md
    ├── TASK_bar.md
    └── ...
```

## Partial Runs

Skip phases for debugging or resuming:

```bash
# Resume from existing plan
python hol_pipeline.py --theorem X --skip-plan --plan my_plan.md

# Just prove (plan and sketch exist)
python hol_pipeline.py --theorem X --skip-plan --skip-sketch
```

## Phase Coordination

| Phase | Input | Output |
|-------|-------|--------|
| Plan | Goal string | plan.md |
| Sketch | plan.md | .sml + TASK_*.md |
| Prove | TASK_*.md | Completed proofs |

Each phase is independent - can be run separately or chained.

## Reconstruction Notes

- Imports and calls the phase runners directly
- Output goes to .hol_pipeline/ subdirectory
- Smaller max_messages for pipeline (50 vs 100)
- Fails fast on any phase failure
- Task files found by glob pattern
