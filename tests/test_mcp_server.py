"""Test the HOL MCP server tools."""

import shutil

import pytest
from pathlib import Path

from hol_mcp_server import (
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_proof_state as _hol_proof_state,
    hol_sessions as _hol_sessions,
    hol_stop as _hol_stop,
    hol_log as _hol_log,
    hol_logs as _hol_logs,
    hol_build as _hol_build,
)

# Unwrap FunctionTool to get actual functions
hol_start = _hol_start.fn
hol_send = _hol_send.fn
hol_proof_state = _hol_proof_state.fn
hol_sessions = _hol_sessions.fn
hol_stop = _hol_stop.fn
hol_log = _hol_log.fn
hol_logs = _hol_logs.fn
hol_build = _hol_build.fn

FIXTURES_DIR = Path(__file__).parent / "fixtures"


@pytest.fixture
def workdir():
    return str(FIXTURES_DIR)


async def test_session_lifecycle(workdir):
    """Test basic session start/list/send/stop."""
    result = await hol_start(workdir=workdir, name="test")
    assert "Session 'test' started" in result
    assert "HOL started (PID" in result

    try:
        result = await hol_sessions()
        assert "test" in result
        assert "running" in result

        result = await hol_send(session="test", command="1 + 1;")
        assert "val it = 2" in result
    finally:
        result = await hol_stop(session="test")
        assert "Session 'test' stopped" in result


async def test_goaltree_mode(workdir):
    """Test goaltree mode proving."""
    await hol_stop(session="gt_test")
    await hol_start(workdir=workdir, name="gt_test")

    try:
        result = await hol_send(session="gt_test", command="gt `1 + 1 = 2`;")
        assert "Proof manager status: 1 proof" in result
        assert "Initial goal:" in result

        result = await hol_send(session="gt_test", command='etq "EVAL_TAC";')
        assert "OK" in result

        result = await hol_proof_state(session="gt_test")
        assert "=== Proof tree (p()) ===" in result
        assert "=== Current goals (top_goals()) ===" in result
        assert "val it = []: goal list" in result  # No remaining goals
    finally:
        await hol_stop(session="gt_test")


async def test_db_search(workdir):
    """Test theorem database search."""
    await hol_stop(session="db_test")
    await hol_start(workdir=workdir, name="db_test")

    try:
        result = await hol_send(session="db_test", command='DB.find "ADD";', timeout=15)
        assert "ADD" in result
        assert "⊢" in result  # Theorem statements contain turnstile
    finally:
        await hol_stop(session="db_test")


async def test_build_and_logs(workdir):
    """Test hol_build generates logs, then test hol_logs/hol_log."""
    # Clean build artifacts to ensure fresh build
    hol_dir = Path(workdir) / ".hol"
    if hol_dir.exists():
        shutil.rmtree(hol_dir)
    for f in Path(workdir).glob("*.uo"):
        f.unlink()
    for f in Path(workdir).glob("*.ui"):
        f.unlink()
    for f in Path(workdir).glob("*Theory.*"):
        f.unlink()

    result = await hol_build(workdir=workdir, target="testTheory")
    assert "Build succeeded" in result
    assert "testTheory" in result

    result = await hol_logs(workdir=workdir)
    assert "Build logs:" in result
    assert "testTheory" in result

    result = await hol_log(workdir=workdir, theory="testTheory", limit=500)
    assert 'theory "test"' in result.lower()

    result = await hol_log(workdir=workdir, theory="test", limit=500)
    assert 'theory "test"' in result.lower()


async def test_build_failure_includes_logs(workdir):
    """Test that build failure includes log output."""
    # Clean to ensure fresh build attempt
    hol_dir = Path(workdir) / ".hol"
    if hol_dir.exists():
        shutil.rmtree(hol_dir)

    result = await hol_build(workdir=workdir, target="failTheory")
    assert "Build failed" in result
    assert "=== Build Logs ===" in result
    assert "failTheory" in result


async def test_log_nonexistent(workdir):
    """Test hol_log for non-existent theory."""
    result = await hol_log(workdir=workdir, theory="nonexistent")
    assert "Log not found: nonexistent" in result
    assert "Available:" in result
