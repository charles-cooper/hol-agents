#!/usr/bin/env python3
"""Codex implements, Claude validates.

Generic implementation/validation loop:
- Codex: --full-auto, workspace-write sandbox
- Claude: validates, commits when ready, or provides feedback

Usage:
    cd /path/to/project && ./codex_claude_loop.py TASK.md
"""

import argparse
import shutil
import subprocess
import sys
from pathlib import Path


def check_dependencies():
    """Verify required binaries are available."""
    missing = []
    if not shutil.which("codex"):
        missing.append("codex")
    if not shutil.which("claude"):
        missing.append("claude")
    if missing:
        print(f"Missing required binaries: {', '.join(missing)}")
        print("Install codex: npm install -g @openai/codex")
        print("Install claude: npm install -g @anthropic-ai/claude-code")
        sys.exit(1)


def run_cmd(cmd, **kw) -> subprocess.CompletedProcess:
    """Run command, return CompletedProcess."""
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def get_head_sha(workdir: Path) -> str:
    """Get current HEAD SHA."""
    result = run_cmd(["git", "rev-parse", "HEAD"], cwd=workdir)
    return result.stdout.strip()


def main():
    parser = argparse.ArgumentParser(
        description="Codex implements, Claude validates"
    )
    parser.add_argument("task", type=Path, help="Task file path")
    parser.add_argument("--max-iter", type=int, default=50, help="Max iterations (default: 50)")
    parser.add_argument("--dry-run", action="store_true", help="Print prompts without running")
    parser.add_argument("--verbose", "-v", action="store_true", help="Show full prompts")
    args = parser.parse_args()

    check_dependencies()

    if not args.task.exists():
        print(f"Task file not found: {args.task}")
        return 1

    # Validate cwd is a git repo
    workdir = Path.cwd()
    if not (workdir / ".git").exists():
        print(f"Not a git repo: {workdir}")
        return 1

    task_content = args.task.read_text()
    max_iter = args.max_iter

    # Setup paths
    scratch_dir = workdir / ".agent-files"
    scratch_dir.mkdir(exist_ok=True)
    summary_file = scratch_dir / "codex_summary.md"

    print(f"Task: {args.task}")
    print(f"Max iterations: {max_iter}")
    print()

    feedback = ""

    for i in range(max_iter):
        print(f"\n{'='*60}")
        print(f"Iteration {i+1}/{max_iter}")
        print("=" * 60)

        # Build Codex prompt
        codex_prompt = f"""## Task
{task_content}

## Secondary Goals
- File size: 200-650 lines per file
- Build time: <10s per file

## Instructions
First, restate the goal in your own words and outline your implementation plan. Then implement fully. Keep going until the task is completely resolved.

Do NOT commit - validation and commit is handled separately.
"""
        if feedback:
            codex_prompt += f"\n## Previous Validation Feedback\nAddress this feedback:\n{feedback}"

        if args.dry_run:
            print(f"[DRY RUN] Codex prompt:\n{codex_prompt}")
            return 0

        if args.verbose:
            print(f"\n[CODEX PROMPT]\n{codex_prompt}\n")

        # 1. Codex implements
        print("\n[CODEX] Implementing...")
        result = run_cmd(
            ["codex", "exec", "--full-auto", "-o", str(summary_file)],
            input=codex_prompt,
        )
        if result.returncode != 0:
            print(f"[CODEX ERROR]\n{result.stderr}")
            feedback = f"Codex failed with error:\n{result.stderr}"
            continue

        summary = summary_file.read_text() if summary_file.exists() else "(no summary generated)"
        print(f"[CODEX SUMMARY]\n{summary}")

        # 2. Claude validates (and commits if ready)
        print("\n[CLAUDE] Validating...")
        head_before = get_head_sha(workdir)

        validation_prompt = f"""ultrathink

You are the validation gate in a Codex->Claude loop. Be thorough--bugs that pass you ship to production.

## Task
{task_content}

## Codex Summary
{summary}

## Instructions

Read the source files. Run builds/tests as appropriate for the project. Verify:
1. Implementation matches task requirements
2. Tests pass (run them)
3. No bugs or issues
4. No dead code (but only flag this after everything else works - some code may just not be wired yet)

If the implementation is correct and complete:
- Stage specific files (git add <file> - NEVER use git add . or stage directories)
- Commit with a good message (subject <50 chars, body wraps at 72 chars)
- Say COMPLETE

If there are issues:
- Provide specific feedback for the next Codex iteration
- Do NOT commit

If the task cannot be completed as specified:
- Say BLOCKED and explain why
"""

        if args.verbose:
            print(f"\n[VALIDATION PROMPT]\n{validation_prompt}\n")

        result = run_cmd(
            ["claude", "-p", "--model", "opus", "--disallowedTools", "Edit,Write"],
            input=validation_prompt,
            cwd=workdir,
        )
        if result.returncode != 0:
            print(f"[CLAUDE ERROR]\n{result.stderr}")
            continue

        validation = result.stdout
        print(f"\n[VALIDATION]\n{validation}")

        # Check if Claude committed
        head_after = get_head_sha(workdir)
        if head_after != head_before:
            print(f"\n[COMPLETE] Claude committed: {head_after}")
            return 0

        # Check for BLOCKED
        if "BLOCKED" in validation.upper():
            print("\n[BLOCKED] Task cannot be completed as specified")
            return 1

        # Otherwise, use validation as feedback for next iteration
        feedback = validation

    print(f"\n[FAILED] Max iterations ({max_iter}) reached")
    return 1


if __name__ == "__main__":
    sys.exit(main())
