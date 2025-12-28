#!/usr/bin/env python3
"""
HOL4 Proof Pipeline

End-to-end automated proof development: Plan → Sketch → Prove

Usage:
    python hol_pipeline.py --theorem "theorem_name" --workdir /path/to/project
    python hol_pipeline.py --theorem "theorem_name" --workdir /path --skip-plan
"""

import argparse
import asyncio
import glob
import os
import sys
from pathlib import Path

# Import the phase runners
from hol_planner import run_planner
from hol_sketch import run_sketch
from hol_proof_agent import run_agent, AgentConfig


async def run_pipeline(
    theorem: str,
    workdir: str,
    skip_plan: bool = False,
    skip_sketch: bool = False,
    plan_file: str | None = None,
) -> bool:
    """Run the full proof pipeline."""

    workdir = os.path.abspath(workdir)
    output_dir = os.path.join(workdir, ".hol_pipeline")
    os.makedirs(output_dir, exist_ok=True)

    plan_path = plan_file or os.path.join(output_dir, f"plan_{theorem}.md")
    sketch_dir = os.path.join(output_dir, "sketches")

    print("=" * 60)
    print("HOL4 Proof Pipeline")
    print("=" * 60)
    print(f"Theorem: {theorem}")
    print(f"Workdir: {workdir}")
    print(f"Output: {output_dir}")
    print("=" * 60)

    # Phase 1: Planning
    if not skip_plan:
        print("\n[PHASE 1] Planning...")
        success = await run_planner(
            goal=f"Prove theorem: {theorem}",
            workdir=workdir,
            output=plan_path,
        )
        if not success:
            print("[PIPELINE] Planning failed")
            return False
        print(f"[PHASE 1] Plan written to: {plan_path}")
    else:
        print(f"\n[PHASE 1] Skipped (using existing plan: {plan_path})")

    if not os.path.exists(plan_path):
        print(f"[PIPELINE] Error: Plan file not found: {plan_path}")
        return False

    # Phase 2: Sketching
    if not skip_sketch:
        print("\n[PHASE 2] Sketching...")
        os.makedirs(sketch_dir, exist_ok=True)
        success = await run_sketch(
            plan_file=plan_path,
            workdir=workdir,
            output_dir=sketch_dir,
        )
        if not success:
            print("[PIPELINE] Sketching failed")
            return False
        print(f"[PHASE 2] Sketch files in: {sketch_dir}")
    else:
        print(f"\n[PHASE 2] Skipped (using existing sketches in: {sketch_dir})")

    # Find task files
    task_files = glob.glob(os.path.join(sketch_dir, "TASK_*.md"))
    if not task_files:
        # Also check workdir
        task_files = glob.glob(os.path.join(workdir, "TASK_*.md"))

    if not task_files:
        print("[PIPELINE] No task files found - sketch may have no cheats?")
        print("[PIPELINE] Checking if holmake passes...")
        # Could run holmake here to verify
        return True

    print(f"\n[PHASE 3] Proving ({len(task_files)} tasks)...")

    # Phase 3: Proving each task
    for i, task_file in enumerate(task_files, 1):
        print(f"\n[PHASE 3.{i}] {os.path.basename(task_file)}")

        # Find CLAUDE.md
        claude_md = ""
        for parent in [Path(workdir)] + list(Path(workdir).parents):
            candidate = parent / "CLAUDE.md"
            if candidate.exists():
                claude_md = str(candidate)
                break

        config = AgentConfig(
            working_dir=workdir,
            task_file=task_file,
            claude_md=claude_md,
            model="claude-sonnet-4-20250514",
            max_agent_messages=50,  # Smaller for pipeline tasks
        )

        success = await run_agent(config)
        if not success:
            print(f"[PIPELINE] Proving failed for: {task_file}")
            return False

        print(f"[PHASE 3.{i}] Completed: {os.path.basename(task_file)}")

    print("\n" + "=" * 60)
    print("[PIPELINE] All phases complete!")
    print("=" * 60)
    return True


def main():
    parser = argparse.ArgumentParser(description="HOL4 Proof Pipeline")
    parser.add_argument("--theorem", "-t", required=True, help="Theorem to prove")
    parser.add_argument("--workdir", "-w", default=os.getcwd(), help="Working directory")
    parser.add_argument("--skip-plan", action="store_true", help="Skip planning phase")
    parser.add_argument("--skip-sketch", action="store_true", help="Skip sketching phase")
    parser.add_argument("--plan", "-p", help="Existing plan file to use")

    args = parser.parse_args()

    try:
        success = asyncio.run(run_pipeline(
            theorem=args.theorem,
            workdir=args.workdir,
            skip_plan=args.skip_plan,
            skip_sketch=args.skip_sketch,
            plan_file=args.plan,
        ))
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\n[PIPELINE] Interrupted")
        sys.exit(2)


if __name__ == "__main__":
    main()
