#!/usr/bin/env python3
"""
HOL4 Proof Planner

Autonomous agent for creating rigorous mathematical proof plans.
Uses the planner methodology as system prompt.

Usage:
    python hol_planner.py --goal "prove theorem X" [--workdir /path]
    python hol_planner.py --goal "prove theorem X" --output plan.md
"""

import argparse
import asyncio
import os
import sys
from pathlib import Path

from claude_agent_sdk import ClaudeAgentOptions, ClaudeSDKClient, ResultMessage


def read_file(path: str) -> str:
    """Read a file, return empty string on error."""
    try:
        with open(path, 'r') as f:
            return f.read()
    except Exception:
        return ""


def build_system_prompt() -> str:
    """Load planner methodology as system prompt."""
    script_dir = Path(__file__).parent
    prompt_path = script_dir / "prompts" / "hol4" / "planner.md"
    prompt = read_file(str(prompt_path))

    if not prompt:
        raise RuntimeError(f"Failed to load planner prompt: {prompt_path}")

    return prompt


async def run_planner(goal: str, workdir: str, output: str | None = None) -> bool:
    """Run the planner agent until it produces a plan."""

    system_prompt = build_system_prompt()

    print(f"[PLANNER] Starting...")
    print(f"[PLANNER] Goal: {goal}")
    print(f"[PLANNER] Workdir: {workdir}")

    opts = ClaudeAgentOptions(
        cwd=workdir,
        model="claude-sonnet-4-20250514",  # Sonnet for bounded tasks
        system_prompt=system_prompt,
        allowed_tools=["Read", "Grep", "Glob", "Task", "Write", "Edit"],
        disallowed_tools=["Bash", "TodoRead", "TodoWrite"],
    )

    task_prompt = f"""## Planning Task

Create a rigorous mathematical proof plan for:

{goal}

Follow the methodology in your system prompt exactly:
1. Analyze the goal
2. Construct argument skeleton
3. Validate ALL claims (spawn subagents as needed)
4. Deliver PROVABLE / NOT PROVABLE / UNKNOWN verdict

When complete, output "PLAN_COMPLETE:" followed by a summary.
"""
    if output:
        task_prompt += f"\nWrite the final plan to: {output}"

    try:
        async with ClaudeSDKClient(opts) as client:
            print(f"[PLANNER] Sending task...")
            await client.query(task_prompt)

            async for message in client.receive_messages():
                msg_type = type(message).__name__

                # Print content
                if hasattr(message, 'content'):
                    for block in message.content:
                        if hasattr(block, 'text') and block.text:
                            print(f"[PLANNER] {block.text[:200]}...")

                            if "PLAN_COMPLETE:" in block.text:
                                print(f"\n[PLANNER] Done!")
                                return True

                # Handle result
                if isinstance(message, ResultMessage):
                    if message.result:
                        print(f"[RESULT] {message.result}")
                    # Continue prompting
                    await client.query("Continue planning. Output PLAN_COMPLETE: when done.")

    except KeyboardInterrupt:
        print("\n[PLANNER] Interrupted")
        return False

    return False


def main():
    parser = argparse.ArgumentParser(description="HOL4 Proof Planner")
    parser.add_argument("--goal", "-g", required=True, help="What to prove")
    parser.add_argument("--workdir", "-w", default=os.getcwd(), help="Working directory")
    parser.add_argument("--output", "-o", help="Output file for plan")

    args = parser.parse_args()

    print("=" * 60)
    print("HOL4 Proof Planner")
    print("=" * 60)

    success = asyncio.run(run_planner(args.goal, args.workdir, args.output))
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
