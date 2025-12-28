#!/usr/bin/env python3
"""
HOL4 Proof Sketch Implementation

Autonomous agent for translating proof plans into HOL4 sketches.
Creates SML files with cheats + task files for proof subagents.

Usage:
    python hol_sketch.py --plan plan.md --workdir /path/to/project
    python hol_sketch.py --plan plan.md --workdir /path --output-dir sketches/
"""

import argparse
import asyncio
import os
import sys
from pathlib import Path

from claude_agent_sdk import ClaudeAgentOptions, ClaudeSDKClient, ResultMessage

# Import MCP server for holmake access
from hol_mcp_server import mcp as hol_mcp


def read_file(path: str) -> str:
    """Read a file, return empty string on error."""
    try:
        with open(path, 'r') as f:
            return f.read()
    except Exception:
        return ""


def build_system_prompt() -> str:
    """Load sketch implementation methodology as system prompt."""
    script_dir = Path(__file__).parent
    prompt_path = script_dir / "prompts" / "hol4" / "sketch_impl.md"
    prompt = read_file(str(prompt_path))

    if not prompt:
        raise RuntimeError(f"Failed to load sketch prompt: {prompt_path}")

    return prompt


# MCP server configuration
MCP_SERVER_CONFIG = {
    "hol": {
        "type": "sdk",
        "name": "hol",
        "instance": hol_mcp._mcp_server,
    }
}


async def run_sketch(plan_file: str, workdir: str, output_dir: str | None = None) -> bool:
    """Run the sketch agent until it produces SML + task files."""

    system_prompt = build_system_prompt()
    plan_content = read_file(plan_file)

    if not plan_content:
        print(f"[SKETCH] Error: Could not read plan file: {plan_file}")
        return False

    print(f"[SKETCH] Starting...")
    print(f"[SKETCH] Plan: {plan_file}")
    print(f"[SKETCH] Workdir: {workdir}")

    opts = ClaudeAgentOptions(
        cwd=workdir,
        model="claude-sonnet-4-20250514",  # Sonnet for bounded tasks
        system_prompt=system_prompt,
        allowed_tools=["Read", "Write", "Edit", "Grep", "Glob", "Task", "mcp__hol__*"],
        disallowed_tools=["Bash", "TodoRead", "TodoWrite"],
        mcp_servers=MCP_SERVER_CONFIG,
    )

    task_prompt = f"""## Sketch Implementation Task

Create a HOL4 proof sketch from this plan:

{plan_content}

Follow the methodology in your system prompt exactly:
1. Split into context-window-sized subtasks if needed
2. Create SML files that COMPILE (verify with holmake)
3. Every theorem needs "WHY THIS IS TRUE" comment
4. Create TASK_*.md files for each cheat

Working directory: {workdir}
"""
    if output_dir:
        task_prompt += f"\nOutput directory: {output_dir}"

    task_prompt += "\n\nWhen complete, output \"SKETCH_COMPLETE:\" followed by list of files created."

    try:
        async with ClaudeSDKClient(opts) as client:
            print(f"[SKETCH] Sending task...")
            await client.query(task_prompt)

            async for message in client.receive_messages():
                msg_type = type(message).__name__

                # Print content
                if hasattr(message, 'content'):
                    for block in message.content:
                        if hasattr(block, 'text') and block.text:
                            print(f"[SKETCH] {block.text[:200]}...")

                            if "SKETCH_COMPLETE:" in block.text:
                                print(f"\n[SKETCH] Done!")
                                return True

                # Handle result
                if isinstance(message, ResultMessage):
                    if message.result:
                        print(f"[RESULT] {message.result}")
                    # Continue prompting
                    await client.query("Continue sketching. Output SKETCH_COMPLETE: when done.")

    except KeyboardInterrupt:
        print("\n[SKETCH] Interrupted")
        return False

    return False


def main():
    parser = argparse.ArgumentParser(description="HOL4 Proof Sketch Implementation")
    parser.add_argument("--plan", "-p", required=True, help="Plan file to implement")
    parser.add_argument("--workdir", "-w", default=os.getcwd(), help="Working directory")
    parser.add_argument("--output-dir", "-o", help="Output directory for sketch files")

    args = parser.parse_args()

    print("=" * 60)
    print("HOL4 Proof Sketch Implementation")
    print("=" * 60)

    success = asyncio.run(run_sketch(args.plan, args.workdir, args.output_dir))
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
