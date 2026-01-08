#!/usr/bin/env python3
"""Codex implements, Claude validates.

Generic implementation/validation loop:
- Codex: --full-auto, workspace-write sandbox
- Claude: validates implementation (can read/run commands, not edit)

Usage:
    cd /path/to/project && ./codex_claude_loop.py TASK.md -b "make test"
"""

import argparse
import re
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
    """Run command, return CompletedProcess. Never raises.

    No timeout: agents (codex/claude) may run for extended periods during
    complex tasks. Callers should not artificially limit execution time.
    """
    try:
        return subprocess.run(cmd, capture_output=True, text=True, **kw)
    except Exception as e:
        return subprocess.CompletedProcess(cmd, returncode=-1, stdout="", stderr=str(e))


def extract_verdict(text: str) -> str:
    """Extract verdict from first 10 non-empty lines. Default NEEDS_WORK.

    Handles common formats: "APPROVED", "- APPROVED", "VERDICT: APPROVED", etc.
    """
    pattern = re.compile(r'^\s*[-*]?\s*(?:VERDICT:?\s*)?(APPROVED|NEEDS_WORK|BLOCKED)', re.IGNORECASE)
    lines = [l for l in text.split('\n') if l.strip()][:10]
    for line in lines:
        match = pattern.match(line)
        if match:
            return match.group(1).upper()
    return "NEEDS_WORK"


def main():
    parser = argparse.ArgumentParser(
        description="Codex implements, Claude validates"
    )
    parser.add_argument("task", type=Path, help="Task file path")
    parser.add_argument("--build", "-b", help="Build command to run after implementation")
    parser.add_argument("--max-iter", type=int, default=5, help="Max iterations (default: 5)")
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

    # Require clean worktree so git add . only stages Codex's changes
    result = run_cmd(["git", "status", "--porcelain"], cwd=workdir)
    if result.stdout.strip():
        print(f"Workdir has uncommitted changes - commit or stash first:")
        print(result.stdout)
        return 1

    task_content = args.task.read_text()
    build_cmd = args.build
    max_iter = args.max_iter

    # Setup paths
    scratch_dir = workdir / ".agent-files"
    scratch_dir.mkdir(exist_ok=True)
    summary_file = scratch_dir / "codex_summary.md"

    print(f"Task: {args.task}")
    print(f"Workdir: {workdir}")
    print(f"Build: {build_cmd or 'none'}")
    print(f"Max iterations: {max_iter}")
    print()

    feedback = ""
    blocked_count = 0

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
            ["codex", "exec", "--full-auto", "-C", str(workdir), "-o", str(summary_file)],
            input=codex_prompt,
        )
        if result.returncode != 0:
            print(f"[CODEX ERROR]\n{result.stderr}")
            feedback = f"Codex failed with error:\n{result.stderr}"
            continue

        summary = summary_file.read_text() if summary_file.exists() else "(no summary generated)"
        print(f"[CODEX SUMMARY]\n{summary}")

        # 2. Build (if configured)
        build_ok = True
        build_output = ""
        if build_cmd:
            print(f"\n[BUILD] Running: {build_cmd}")
            result = run_cmd(build_cmd, shell=True, cwd=workdir)
            build_output = result.stdout + result.stderr
            build_ok = result.returncode == 0
            print(f"[BUILD] {'PASS' if build_ok else 'FAIL'}")
            if not build_ok:
                print(f"[BUILD OUTPUT]\n{build_output}")

        # 3. Claude validates
        print("\n[CLAUDE] Validating...")
        validation_prompt = f"""You are the validation gate in a Codex->Claude loop. Your approval commits code; your rejection triggers another Codex iteration. Be thorough--bugs that pass you ship to production.

## Task
{task_content}

## Codex Summary
{summary}

## Build Result
{"PASS" if build_ok else "FAIL"}
{build_output if not build_ok else ""}

## Instructions

Read the actual source files. Verify:
1. Implementation matches task requirements
2. Build passes
3. No bugs or issues

Respond with exactly one verdict on the FIRST LINE:
- APPROVED: Task complete and correct
- NEEDS_WORK: Specific feedback for next iteration
- BLOCKED: Task cannot be completed as specified
"""

        if args.verbose:
            print(f"\n[VALIDATION PROMPT]\n{validation_prompt}\n")

        result = run_cmd(
            ["claude", "-p", "--model", "opus", "--disallowedTools", "Edit,Write"],
            input=f"ultrathink\n\n{validation_prompt}",
            cwd=workdir,
        )
        if result.returncode != 0:
            print(f"[CLAUDE ERROR]\n{result.stderr}")
            # Can't validate - retry iteration
            continue

        validation = result.stdout
        print(f"\n[VALIDATION]\n{validation}")

        # 4. Check verdict
        verdict = extract_verdict(validation)
        print(f"\n[VERDICT] {verdict}")

        if verdict == "APPROVED":
            # Build must pass to commit
            if not build_ok:
                print("[REJECTED] Cannot commit with failing build")
                feedback = "Build is failing. APPROVED verdict invalid - fix build first."
                continue

            # Check if there are changes to commit
            result = run_cmd(["git", "status", "--porcelain"], cwd=workdir)
            if not result.stdout.strip():
                print("\n[COMPLETE] Task approved (no changes to commit)")
                return 0

            # Stage and show what's staged
            run_cmd(["git", "add", "."], cwd=workdir)
            result = run_cmd(["git", "diff", "--cached", "--stat"], cwd=workdir)
            print(f"\n[STAGED]\n{result.stdout}")

            # Generate commit message
            diff_result = run_cmd(["git", "diff", "--cached"], cwd=workdir)
            result = run_cmd(
                ["claude", "-p", "--model", "opus", "--disallowedTools", "Edit,Write"],
                input=f"ultrathink\n\nWrite ONLY a git commit message. Subject line <72 chars, optional body after blank line. No explanation or preamble.\n\nDiff:\n{diff_result.stdout}",
                cwd=workdir,
            )

            if result.returncode == 0 and result.stdout.strip():
                commit_msg = result.stdout.strip()
            else:
                commit_msg = f"chore: automated changes for {args.task.stem}"
                print(f"[WARN] Using fallback commit message")

            result = run_cmd(["git", "commit", "-m", commit_msg], cwd=workdir)
            if result.returncode != 0:
                print(f"[COMMIT FAILED]\n{result.stderr}")
                return 1

            print(f"\n[COMPLETE] Committed:\n{commit_msg}")
            return 0

        elif verdict == "BLOCKED":
            blocked_count += 1
            print(f"[BLOCKED] Count: {blocked_count}/2")
            if blocked_count >= 2:
                print("\n[ABORT] Two consecutive BLOCKED verdicts - giving up")
                return 1
            feedback = validation

        else:
            # NEEDS_WORK or unclear - continue with feedback
            blocked_count = 0
            feedback = validation

    print(f"\n[FAILED] Max iterations ({max_iter}) reached")
    return 1


if __name__ == "__main__":
    sys.exit(main())
