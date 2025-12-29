#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
from dataclasses import dataclass
from pathlib import Path
from datetime import datetime
from typing import Optional

from fastmcp import FastMCP

from hol_session import HOLSession, HOLDIR
from hol_cursor import ProofCursor


@dataclass
class SessionEntry:
    """Registry entry for a HOL session."""
    session: HOLSession
    started: datetime
    workdir: Path
    cursor: Optional[ProofCursor] = None
    holmake_env: Optional[dict] = None  # env vars for holmake (auto-captured on success)


mcp = FastMCP("hol", instructions="""HOL4 theorem prover.
holmake: build. hol_start/hol_send: interactive. hol_cursor_*: file-based proofs.""")
_sessions: dict[str, SessionEntry] = {}
_agent_state = None  # Set by proof_agent for direct holmake_env capture


def set_agent_state(state) -> None:
    """Register agent state for holmake_env capture. No-op if different process."""
    global _agent_state
    _agent_state = state


def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found."""
    entry = _sessions.get(name)
    return entry.session if entry else None


def _get_cursor(name: str) -> Optional[ProofCursor]:
    """Get cursor from registry, or None if not found."""
    entry = _sessions.get(name)
    return entry.cursor if entry else None


def _session_age(name: str) -> str:
    """Get human-readable session age."""
    entry = _sessions.get(name)
    if not entry:
        return "unknown"
    started = entry.started
    delta = datetime.now() - started
    secs = int(delta.total_seconds())
    if secs < 60:
        return f"{secs}s"
    elif secs < 3600:
        return f"{secs // 60}m"
    else:
        return f"{secs / 3600:.1f}h"


@mcp.tool()
async def hol_start(workdir: str, name: str = "default") -> str:
    """Start HOL session (idempotent - returns existing if running).

    Args:
        workdir: Working directory for HOL (where Holmakefile is)
        name: Session identifier (use simple names like 'main')

    Returns: Session status and current proof state
    """
    # If session exists and is running, return its state
    if name in _sessions:
        session = _sessions[name].session
        if session.is_running:
            goals = await session.send("top_goals();", timeout=10)
            return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"
        # Dead session - clean up
        del _sessions[name]

    # Validate workdir
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Working directory does not exist: {workdir}"

    # Create session
    session = HOLSession(str(workdir_path))

    try:
        result = await session.start()
    except Exception as e:
        return f"ERROR starting HOL: {e}"

    if not session.is_running:
        return f"ERROR: HOL failed to start. Output: {result}"

    # Register session
    _sessions[name] = SessionEntry(session, datetime.now(), workdir_path)

    return f"Session '{name}' started. {result}\nWorkdir: {workdir_path}"


@mcp.tool()
async def hol_sessions() -> str:
    """List all active HOL sessions with their workdir, age, status, cursor."""
    if not _sessions:
        return "No active sessions."

    lines = ["SESSION      WORKDIR                                    AGE     STATUS   CURSOR"]
    lines.append("-" * 95)

    for name, entry in _sessions.items():
        status = "running" if entry.session.is_running else "dead"
        age = _session_age(name)
        workdir_str = str(entry.workdir)
        if len(workdir_str) > 40:
            workdir_str = "..." + workdir_str[-37:]

        # Cursor info
        if entry.cursor:
            cs = entry.cursor.status
            cursor_str = f"{cs['current']} ({cs['position']})" if cs['current'] else "(none)"
        else:
            cursor_str = "(none)"

        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {status:<8} {cursor_str}")

    return "\n".join(lines)


@mcp.tool()
async def hol_send(session: str, command: str, timeout: int = 5) -> str:
    """Send SML to HOL.

      gt `goal`;         (* start proof - not g *)
      etq "tactic";      (* apply - not e, records for p() *)
      p();               (* extract proof script *)
      backup(); drop();  (* undo / abandon *)

    Args: session, command, timeout (default 5, max 600)
    """
    s = _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    # Validate timeout
    if timeout < 1:
        timeout = 1
    elif timeout > 600:
        timeout = 600

    return await s.send(command, timeout=timeout)


@mcp.tool()
async def hol_interrupt(session: str) -> str:
    """Send SIGINT to abort runaway tactic.

    Args:
        session: Session name from hol_start

    Returns: Confirmation message
    """
    s = _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died."

    s.interrupt()

    # Try to read any output
    await asyncio.sleep(0.5)

    return f"Sent SIGINT to session '{session}'. The tactic should be interrupted."


@mcp.tool()
async def hol_stop(session: str) -> str:
    """Terminate HOL session.

    Args:
        session: Session name from hol_start

    Returns: Confirmation message
    """
    entry = _sessions.pop(session, None)
    if entry:
        await entry.session.stop()
        return f"Session '{session}' stopped."
    return f"Session '{session}' not found."


@mcp.tool()
async def hol_restart(session: str) -> str:
    """Restart HOL session (stop + start, preserves workdir).

    Use when HOL state is corrupted or you need to reload theories after file changes.

    Args:
        session: Session name to restart

    Returns: Same as hol_start (session info + proof state)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found."

    workdir = entry.workdir
    await hol_stop.fn(session)
    return await hol_start.fn(workdir=str(workdir), name=session)


@mcp.tool()
async def holmake(workdir: str, target: str = None, env: dict = None, log_limit: int = 1024, timeout: int = 90) -> str:
    """Run Holmake --qof in directory.

    Args:
        workdir: Directory containing Holmakefile
        target: Optional specific target to build
        env: Optional environment variables (e.g. {"MY_VAR": "/some/path"})
        log_limit: Max bytes per log file to include on failure (default 1024)
        timeout: Max seconds to wait (default 90, max 1800)

    Returns: Holmake output (stdout + stderr). On failure, includes recent build logs.

    Design note: Consider whether env vars should be set once at proof_agent
    session startup (via CLI --env flag) rather than per-build call.
    """
    # Validate timeout
    timeout = max(1, min(timeout, 1800))
    import os as _os
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Directory does not exist: {workdir}"

    holmake = HOLDIR / "bin" / "Holmake"
    if not holmake.exists():
        return f"ERROR: Holmake not found at {holmake}"

    logs_dir = workdir_path / ".hol" / "logs"

    # Snapshot existing log mtimes before build
    pre_logs = {}
    if logs_dir.exists():
        for log_file in logs_dir.iterdir():
            if log_file.is_file():
                pre_logs[log_file.name] = log_file.stat().st_mtime

    cmd = [str(holmake), "--qof"]
    if target:
        cmd.append(target)

    # Build environment
    proc_env = _os.environ.copy()
    if env:
        proc_env.update(env)

    proc = None
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            cwd=workdir_path,
            env=proc_env,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
        )

        stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout)
        output = stdout.decode("utf-8", errors="replace")

        if proc.returncode == 0:
            if env:
                # Store env in matching session entries for auto-holmake at startup
                for entry in _sessions.values():
                    if entry.workdir == workdir_path:
                        entry.holmake_env = env
                # Direct capture to agent state (same-process only)
                if _agent_state is not None:
                    _agent_state.holmake_env = env
                    _agent_state.save()
            return f"Build succeeded.\n\n{output}"

        # Build failed - append relevant logs
        result = f"Build failed (exit code {proc.returncode}).\n\n{output}"

        if logs_dir.exists():
            # Find logs modified during build
            modified = []
            for log_file in logs_dir.iterdir():
                if not log_file.is_file():
                    continue
                mtime = log_file.stat().st_mtime
                if log_file.name not in pre_logs or mtime > pre_logs[log_file.name]:
                    modified.append((log_file, mtime))

            if modified:
                # Sort by mtime descending (most recent first)
                modified.sort(key=lambda x: -x[1])
                result += "\n\n=== Build Logs ===\n"
                for log_file, _ in modified[:3]:
                    content = log_file.read_text(errors="replace")
                    if len(content) > log_limit:
                        content = f"...(truncated, showing last {log_limit} bytes)...\n" + content[-log_limit:]
                    result += f"\n--- {log_file.name} ---\n{content}\n"

        return result

    except asyncio.TimeoutError:
        if proc:
            proc.kill()
        return f"ERROR: Build timed out after {timeout}s."
    except Exception as e:
        if proc and proc.returncode is None:
            proc.kill()
        return f"ERROR: {e}"


@mcp.tool()
async def hol_log(workdir: str, theory: str, limit: int = 1024) -> str:
    """Read build log for a specific theory.

    Use after holmake to inspect warnings or errors in detail.

    Args:
        workdir: Directory containing .hol/logs/
        theory: Theory name (e.g., "fooTheory")
        limit: Max bytes to return (default 1024, 0 for unlimited)

    Returns: Log file contents (tail if truncated)
    """
    workdir_path = Path(workdir).resolve()
    log_file = workdir_path / ".hol" / "logs" / theory

    if not log_file.exists():
        # Try without "Theory" suffix
        log_file = workdir_path / ".hol" / "logs" / f"{theory}Theory"
        if not log_file.exists():
            available = []
            logs_dir = workdir_path / ".hol" / "logs"
            if logs_dir.exists():
                available = [f.name for f in logs_dir.iterdir() if f.is_file()]
            if available:
                return f"Log not found: {theory}\nAvailable: {', '.join(sorted(available))}"
            return f"Log not found: {theory}\nNo logs in {logs_dir}"

    content = log_file.read_text(errors="replace")
    if limit > 0 and len(content) > limit:
        return f"...(truncated, showing last {limit} bytes)...\n{content[-limit:]}"
    return content


@mcp.tool()
async def hol_logs(workdir: str) -> str:
    """List available build logs.

    Args:
        workdir: Directory containing .hol/logs/

    Returns: List of log files with sizes and modification times
    """
    workdir_path = Path(workdir).resolve()
    logs_dir = workdir_path / ".hol" / "logs"

    if not logs_dir.exists():
        return f"No logs directory: {logs_dir}"

    logs = []
    for log_file in sorted(logs_dir.iterdir()):
        if log_file.is_file():
            stat = log_file.stat()
            size = stat.st_size
            mtime = datetime.fromtimestamp(stat.st_mtime).strftime("%H:%M:%S")
            logs.append(f"  {log_file.name}: {size} bytes, modified {mtime}")

    if not logs:
        return "No log files found."
    return "Build logs:\n" + "\n".join(logs)


# =============================================================================
# Cursor Tools (for multi-theorem files)
# =============================================================================


@mcp.tool()
async def hol_cursor_init(file: str, session: str = "default", workdir: str = None, start_at: str = None) -> str:
    """Initialize cursor and start proving a theorem.

    Parses file, finds theorems with cheats, loads HOL context, and enters
    goaltree mode for the specified theorem (or first cheat if not specified).

    Auto-starts HOL session if needed.

    Args:
        file: Path to .sml file containing theorems
        session: Session name (default: "default")
        workdir: Working directory for HOL (default: file's parent directory)
        start_at: Theorem name to start at (default: first cheat)

    Returns: Status showing current position, theorems found, and current goals
    """
    # Validate file first
    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    # Auto-start session if needed
    s = _get_session(session)
    if not s or not s.is_running:
        wd = workdir or str(file_path.parent)
        start_result = await hol_start.fn(workdir=wd, name=session)
        if start_result.startswith("ERROR"):
            return start_result
        s = _get_session(session)

    cursor = ProofCursor(file_path, s)
    result = await cursor.initialize()

    _sessions[session].cursor = cursor

    # Jump to specific theorem if requested
    if start_at:
        thm = cursor.goto(start_at)
        if not thm:
            available = [t.name for t in cursor.theorems if t.has_cheat]
            return f"ERROR: Theorem '{start_at}' not found.\nAvailable cheats: {', '.join(available)}"
        # Load context up to target theorem
        await cursor.load_context_to(thm.start_line)
        result = f"Positioned at {thm.name} (line {thm.start_line})"

    # Build status
    status = cursor.status
    lines = [
        result,
        "",
        f"File: {status['file']}",
        f"Theorems: {status['position']}",
        f"Remaining cheats: {len(status['cheats'])}",
    ]

    if status['current']:
        lines.append(f"Current: {status['current']} (line {status['current_line']})")

        # Enter goaltree for current theorem
        start_result = await cursor.start_current()
        goals = await s.send("top_goals();", timeout=10)
        lines.append("")
        lines.append(f"=== Proving {status['current']} ===")
        lines.append(start_result)
        lines.append("")
        lines.append("=== Current goals ===")
        lines.append(goals)

    return "\n".join(lines)


@mcp.tool()
async def hol_cursor_status(session: str) -> str:
    """Get current cursor position and status.

    Args:
        session: Session name

    Returns: Current theorem, position, completed list, all remaining cheats
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    status = cursor.status
    lines = [
        f"File: {status['file']}",
        f"Position: {status['position']}",
        f"Current: {status['current']} (line {status['current_line']})" if status['current'] else "Current: None",
        f"Completed: {', '.join(status['completed']) or 'None'}",
        "",
        f"Remaining cheats ({len(status['cheats'])}):",
    ]
    for c in status['cheats']:
        marker = " <--" if c['name'] == status['current'] else ""
        lines.append(f"  {c['name']} (line {c['line']}){marker}")
    return "\n".join(lines)


@mcp.tool()
async def hol_cursor_goto(session: str, theorem_name: str) -> str:
    """Jump to specific theorem by name and enter goaltree.

    Use to skip ahead or go back to a different cheat.
    Drops current proof state before jumping.

    Args:
        session: Session name
        theorem_name: Name of theorem to jump to

    Returns: Theorem info and current goals
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    s = _get_session(session)
    if not s or not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    # Drop current proof state
    await s.send("drop();", timeout=5)

    # Jump to theorem
    thm = cursor.goto(theorem_name)
    if not thm:
        available = [t.name for t in cursor.theorems if t.has_cheat]
        return f"ERROR: Theorem '{theorem_name}' not found.\nAvailable cheats: {', '.join(available)}"

    if not thm.has_cheat:
        return f"WARNING: {theorem_name} has no cheat (already proved)."

    # Load context up to target theorem
    await cursor.load_context_to(thm.start_line)

    # Enter goaltree
    result = await cursor.start_current()
    goals = await s.send("top_goals();", timeout=10)

    return f"Jumped to {theorem_name} (line {thm.start_line})\n{result}\n\n=== Current goals ===\n{goals}"


@mcp.tool()
async def hol_cursor_reenter(session: str) -> str:
    """Re-enter goaltree for current theorem.

    Use after drop() or to retry a failed proof attempt.
    Does NOT advance to next theorem - just re-enters goaltree for current.

    Args:
        session: Session name

    Returns: Confirmation and current goal state
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    s = _get_session(session)
    if not s or not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    result = await cursor.start_current()

    # Also get current goals
    goals = await s.send("top_goals();", timeout=10)

    return f"{result}\n\n=== Current goals ===\n{goals}"


@mcp.tool()
async def hol_cursor_complete(session: str) -> str:
    """Complete current theorem and start proving next.

    Extracts proof from p(), splices into file replacing cheat,
    advances to next theorem with cheat, and enters goaltree for it.

    Args:
        session: Session name

    Returns: Confirmation, next theorem info, and current goals (if any remain)
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    s = _get_session(session)
    if not s or not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    result = await cursor.complete_and_advance()

    # Get status after advancement
    status = cursor.status
    lines = [
        result,
        "",
        f"Remaining cheats: {len(status['cheats'])}",
    ]

    if status['current']:
        # Enter goaltree for next theorem
        start_result = await cursor.start_current()
        goals = await s.send("top_goals();", timeout=10)
        lines.append(f"Next: {status['current']} (line {status['current_line']})")
        lines.append("")
        lines.append(f"=== Proving {status['current']} ===")
        lines.append(start_result)
        lines.append("")
        lines.append("=== Current goals ===")
        lines.append(goals)
    else:
        lines.append("No more theorems with cheats!")

    return "\n".join(lines)


if __name__ == "__main__":
    import argparse
    import logging
    import sys

    parser = argparse.ArgumentParser(description="HOL4 MCP Server")
    parser.add_argument(
        "--transport",
        choices=["stdio", "http", "sse"],
        default="stdio",
        help="Transport protocol (default: stdio)",
    )
    parser.add_argument("--port", type=int, default=8000, help="Port for HTTP/SSE (default: 8000)")
    parser.add_argument("--host", default="127.0.0.1", help="Host for HTTP/SSE (default: 127.0.0.1)")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable debug logging")
    args = parser.parse_args()

    if args.verbose:
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(asctime)s %(levelname)s %(name)s: %(message)s",
            stream=sys.stderr,
        )
        logging.getLogger("mcp").setLevel(logging.DEBUG)

    if args.transport == "stdio":
        mcp.run()
    else:
        print(f"HOL MCP server starting on {args.host}:{args.port} ({args.transport})", file=sys.stderr)
        mcp.run(transport=args.transport, host=args.host, port=args.port)
