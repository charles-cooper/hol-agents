#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
from pathlib import Path
from datetime import datetime
from typing import Optional

from fastmcp import FastMCP

from hol_session import HOLSession, HOLDIR
from hol_cursor import ProofCursor

mcp = FastMCP("hol")
_sessions: dict[str, tuple[HOLSession, datetime, Path]] = {}  # name -> (session, started, workdir)
_cursors: dict[str, ProofCursor] = {}  # session_name -> cursor


def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found."""
    entry = _sessions.get(name)
    return entry[0] if entry else None


def _session_age(name: str) -> str:
    """Get human-readable session age."""
    entry = _sessions.get(name)
    if not entry:
        return "unknown"
    started = entry[1]
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
        session = _sessions[name][0]
        if session.is_running:
            p_out = await session.send("p();", timeout=10)
            goals = await session.send("top_goals();", timeout=10)
            return f"Session '{name}' already running.\n\n=== Proof tree ===\n{p_out}\n\n=== Goals ===\n{goals}"
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
    _sessions[name] = (session, datetime.now(), workdir_path)

    return f"Session '{name}' started. {result}\nWorkdir: {workdir_path}"


@mcp.tool()
async def hol_sessions() -> str:
    """List all active HOL sessions with their workdir, age, status."""
    if not _sessions:
        return "No active sessions."

    lines = ["SESSION      WORKDIR                                    AGE     STATUS"]
    lines.append("-" * 75)

    for name, (session, started, workdir) in _sessions.items():
        status = "running" if session.is_running else "dead"
        age = _session_age(name)
        workdir_str = str(workdir)
        if len(workdir_str) > 40:
            workdir_str = "..." + workdir_str[-37:]
        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {status}")

    return "\n".join(lines)


@mcp.tool()
async def hol_send(session: str, command: str, timeout: int = 120) -> str:
    """Send SML code to HOL.

    Args:
        session: Session name from hol_start
        command: SML code to execute
        timeout: Max seconds to wait (default 120, max 600)

    Returns: HOL output
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
        await entry[0].stop()
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

    workdir = entry[2]
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
async def hol_cursor_init(session: str, file: str) -> str:
    """Initialize cursor for a file with multiple theorems.

    Parses the file, finds theorems with cheats, loads HOL context up to
    the first cheat, and positions the cursor there.

    Args:
        session: Session name from hol_start
        file: Path to .sml file containing theorems

    Returns: Status showing current position and theorems found
    """
    s = _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found."
    if not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    cursor = ProofCursor(file_path, s)
    result = await cursor.initialize()

    _cursors[session] = cursor

    # Build status
    status = cursor.status
    lines = [
        result,
        "",
        f"File: {status['file']}",
        f"Theorems: {status['position']}",
        f"Remaining cheats: {status['remaining_cheats']}",
    ]

    if status['current']:
        lines.append(f"Current: {status['current']} (line {status['current_line']})")

    return "\n".join(lines)


@mcp.tool()
async def hol_cursor_status(session: str) -> str:
    """Get current cursor position and status.

    Args:
        session: Session name

    Returns: Current theorem, position, completed list, remaining cheats
    """
    cursor = _cursors.get(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    status = cursor.status
    lines = [
        f"File: {status['file']}",
        f"Position: {status['position']}",
        f"Current: {status['current']} (line {status['current_line']})" if status['current'] else "Current: None",
        f"Completed: {', '.join(status['completed']) or 'None'}",
        f"Remaining cheats: {status['remaining_cheats']}",
    ]
    return "\n".join(lines)


@mcp.tool()
async def hol_cursor_start(session: str) -> str:
    """Start proving the current theorem.

    Sets up goaltree mode with the theorem's goal and replays any
    tactics that come before the cheat.

    Args:
        session: Session name

    Returns: Confirmation and current goal state
    """
    cursor = _cursors.get(session)
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
    """Complete current theorem and advance to next.

    Extracts the proof from p(), splices it into the file replacing
    the cheat, and moves to the next theorem with a cheat.

    Args:
        session: Session name

    Returns: Confirmation and next theorem info
    """
    cursor = _cursors.get(session)
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
        f"Remaining cheats: {status['remaining_cheats']}",
    ]

    if status['current']:
        lines.append(f"Next: {status['current']} (line {status['current_line']})")
    else:
        lines.append("No more theorems with cheats!")

    return "\n".join(lines)


if __name__ == "__main__":
    mcp.run()
