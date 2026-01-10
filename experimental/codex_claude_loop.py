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
import time
from datetime import datetime
from pathlib import Path


def log(msg: str, file=None):
    """Print with timestamp."""
    ts = datetime.now().strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", file=file or sys.stdout)


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


def main():
    parser = argparse.ArgumentParser(
        description="Codex implements, Claude validates"
    )
    parser.add_argument("task", type=Path, help="Task file path")
    parser.add_argument("--max-iter", type=int, default=50, help="Max iterations (default: 50)")
    parser.add_argument("--dry-run", action="store_true", help="Print prompts without running")
    # TODO: maybe default should be resume, --no-resume or --fresh turns it off
    parser.add_argument("--resume", action="store_true", help="Load previous validation as feedback for Codex")
    parser.add_argument("--validate-only", action="store_true", help="Skip Codex, run Claude validation only")
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
    validation_file = scratch_dir / "claude_validation.md"

    log(f"Task: {args.task}")
    log(f"Max iterations: {max_iter}")

    feedback = ""
    if args.resume and validation_file.exists():
        feedback = validation_file.read_text()
        log("[RESUME] Loaded previous validation as feedback")

    for i in range(max_iter):
        log(f"\n{'='*60}")
        log(f"Iteration {i+1}/{max_iter}")
        log("=" * 60)

        # Build Codex prompt
        codex_prompt = f"""## Task
{task_content}

## Secondary Goals
- File size: 200-650 lines per file
- Build time: <10s per file

## Instructions
First, read any referenced design documents (e.g., DESIGN_*.md files mentioned in the task). The design document is the source of truth - if the task file contains code snippets that contradict the design, follow the design.

Then restate the goal in your own words and outline your implementation plan. Then implement fully. Keep going until the task is completely resolved.

Commit completed chunks of work as you go (stage specific files, never `git add .` or directories).
ONLY modify the task file to check off completed items and list scratch files in use. Use one or more scratch files (e.g. .agent-files/SCRATCH_<slug>.md) for notes/progress.

If you hit a blocker or can't complete, it's ok to stop and explain the issue. Claude will review and provide guidance for the next iteration.
"""
        if feedback:
            codex_prompt += f"\n## Previous Validation Feedback\nAddress this feedback:\n{feedback}"

        if args.dry_run:
            log(f"[DRY RUN] Codex prompt:\n{codex_prompt}")
            return 0

        # Capture baseline commit before Codex runs
        baseline_commit = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True, text=True, cwd=workdir
        ).stdout.strip()

        if args.validate_only:
            # Skip Codex, use existing summary or generate from recent changes
            if summary_file.exists():
                summary = summary_file.read_text()
                log(f"[VALIDATE-ONLY] Using existing summary:\n{summary}")
            else:
                summary = "(no Codex summary - validating current state)"
                log(f"[VALIDATE-ONLY] {summary}")
        else:
            # 1. Codex implements (stream output to terminal for visibility)
            log("[CODEX] Implementing...")
            result = subprocess.run(
                ["codex", "exec", "--full-auto", "-o", str(summary_file)],
                input=codex_prompt,
                text=True,
            )
            if result.returncode != 0:
                feedback = "Codex failed (see output above)"
                continue

            summary = summary_file.read_text() if summary_file.exists() else "(no summary generated)"
            log(f"[CODEX SUMMARY]\n{summary}")

        # 2. Claude validates (and commits if ready)
        log("[CLAUDE] Validating...")

        validation_prompt = f"""ultrathink

You are the validation gate in a Codex->Claude loop. Be thorough--bugs that pass you ship to production.

## Task
{task_content}

## Codex Summary
{summary}

## Baseline
Commit before Codex ran: {baseline_commit}
Use `git diff {baseline_commit}..HEAD` or `git log {baseline_commit}..HEAD` to see what changed.

## Instructions

Read the source files. Run builds/tests as appropriate for the project. Verify:
1. Implementation matches task requirements
2. Tests pass (run them)
3. No bugs or issues
4. No dead code (but only flag this after everything else works - some code may just not be wired yet)

Codex may have already committed work. Commit any additional complete work (stage specific files only, never git add . or directories).

When entire task is done, end with exactly: [COMPLETE]

IF AND ONLY IF THE task requires human intervention (i.e., the theorem actually cannot be proven):
- End your response with exactly: [BLOCKED]
DO NOT RESPOND WITH BLOCKED IF CODEX CAN FIGURE IT OUT

Otherwise your output becomes feedback for the next Codex iteration. Be specific about what files to change and how.
"""

        # Run Claude with retries (keep trying until success)
        validation = None
        attempt = 0
        while validation is None:
            attempt += 1
            result = subprocess.run(
                ["claude", "-p", "--model", "opus"],
                input=validation_prompt,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=workdir,
            )
            if result.returncode == 0:
                validation = result.stdout
                break
            # Log failure to stderr
            log(f"[CLAUDE] Attempt {attempt} failed (exit {result.returncode})", file=sys.stderr)
            if result.stdout:
                log(f"[CLAUDE STDOUT]\n{result.stdout}", file=sys.stderr)
            if result.stderr:
                log(f"[CLAUDE STDERR]\n{result.stderr}", file=sys.stderr)
            # Backoff: wait before retry (cap at 45min)
            delay = min(60 * attempt, 45 * 60)
            log(f"[CLAUDE] Retrying in {delay}s...", file=sys.stderr)
            time.sleep(delay)

        validation_file.write_text(validation)
        log(f"[VALIDATION]\n{validation}")

        # Check for completion markers at end of output
        validation_stripped = validation.strip()
        if validation_stripped.endswith("[COMPLETE]"):
            log("[COMPLETE] Task finished")
            return 0

        if validation_stripped.endswith("[BLOCKED]"):
            log("[BLOCKED] Task cannot be completed as specified")
            return 1

        # Otherwise, use validation as feedback for next iteration
        feedback = validation

        # For validate-only, exit after one pass (no Codex to iterate with)
        if args.validate_only:
            log("[VALIDATE-ONLY] Feedback generated (no Codex iteration)")
            return 2  # Distinct exit code: neither complete nor blocked

    log(f"[FAILED] Max iterations ({max_iter}) reached")
    return 1


if __name__ == "__main__":
    sys.exit(main())
