"""Test the HOL MCP server tools."""

import shutil

import pytest
from pathlib import Path

from hol_mcp_server import (
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_sessions as _hol_sessions,
    hol_stop as _hol_stop,
    hol_log as _hol_log,
    hol_logs as _hol_logs,
    holmake as _holmake,
    hol_cursor_init as _hol_cursor_init,
    hol_cursor_status as _hol_cursor_status,
    hol_cursor_goto as _hol_cursor_goto,
    set_agent_state,
)

# Unwrap FunctionTool to get actual functions
hol_start = _hol_start.fn
hol_send = _hol_send.fn
hol_sessions = _hol_sessions.fn
hol_stop = _hol_stop.fn
hol_log = _hol_log.fn
hol_logs = _hol_logs.fn
holmake = _holmake.fn
hol_cursor_init = _hol_cursor_init.fn
hol_cursor_status = _hol_cursor_status.fn
hol_cursor_goto = _hol_cursor_goto.fn

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

        # Check proof state via hol_send
        result = await hol_send(session="gt_test", command="top_goals();")
        assert "val it = []: goal list" in result  # No remaining goals
    finally:
        await hol_stop(session="gt_test")


async def test_p_output_multiline_integration(workdir):
    """Integration test: parse_p_output handles multi-line val it format from real HOL."""
    from hol_file_parser import parse_p_output

    await hol_stop(session="p_multi_test")
    await hol_start(workdir=workdir, name="p_multi_test")

    try:
        # Create a proof with multiple tactics to produce multi-line p() output
        await hol_send(session="p_multi_test", command="gt `A /\\ B ==> B /\\ A`;")
        await hol_send(session="p_multi_test", command='etq "strip_tac";')
        await hol_send(session="p_multi_test", command='etq "conj_tac";')
        await hol_send(session="p_multi_test", command='etq "first_assum ACCEPT_TAC";')
        await hol_send(session="p_multi_test", command='etq "first_assum ACCEPT_TAC";')

        # p() on complete proof can produce multi-line "val it = ..." format
        result = await hol_send(session="p_multi_test", command="p();")

        # Verify we got multi-line format with ": proof" type annotation
        assert "\n" in result.strip(), f"Expected multi-line output, got: {result!r}"
        assert ": proof" in result, f"Expected complete proof format, got: {result!r}"

        # Check for multi-line val it format: "val it =" on its own line or
        # single-line format with content after "val it = "
        has_multiline_val_it = "val it =\n" in result or "val it = \n" in result
        has_singleline_val_it = "val it = " in result and ": proof" in result

        # Either format is valid - the key is parse_p_output handles it
        assert has_multiline_val_it or has_singleline_val_it, (
            f"Expected val it format, got: {result!r}"
        )

        # Verify parse_p_output handles whatever format HOL produced
        parsed = parse_p_output(result)
        assert parsed is not None, f"parse_p_output failed on: {result!r}"
        assert "strip_tac" in parsed
        assert "conj_tac" in parsed
        assert ": proof" not in parsed  # Type annotation stripped
    finally:
        await hol_stop(session="p_multi_test")


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
    """Test holmake generates logs, then test hol_logs/hol_log."""
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

    result = await holmake(workdir=workdir, target="testTheory")
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

    result = await holmake(workdir=workdir, target="failTheory")
    assert "Build failed" in result
    assert "=== Build Logs ===" in result
    assert "failTheory" in result


async def test_log_nonexistent(workdir):
    """Test hol_log for non-existent theory."""
    result = await hol_log(workdir=workdir, theory="nonexistent")
    assert "Log not found: nonexistent" in result
    assert "Available:" in result


async def test_holmake_env_capture(workdir, tmp_path):
    """Test that holmake captures env to agent state on success."""
    from hol_proof_agent import AgentState

    state_file = tmp_path / "state.json"
    state = AgentState(path=str(state_file))
    set_agent_state(state)

    try:
        # Build with env - should capture and persist
        test_env = {"TEST_VAR": "test_value"}
        result = await holmake(workdir=workdir, target="testTheory", env=test_env)
        assert "Build succeeded" in result
        assert state.holmake_env == test_env
        assert state_file.exists()

        # Reload from disk to verify persistence
        reloaded = AgentState.load(str(state_file))
        assert reloaded.holmake_env == test_env

        # Build without env - should NOT overwrite
        state_file.unlink()
        result = await holmake(workdir=workdir, target="testTheory", env=None)
        assert "Build succeeded" in result
        assert state.holmake_env == test_env  # unchanged
        assert not state_file.exists()  # save not called
    finally:
        set_agent_state(None)


# =============================================================================
# Cursor MCP Tool Tests
# =============================================================================


async def test_cursor_init_start_at(tmp_path):
    """Test hol_cursor_init with start_at parameter."""
    # Copy fixture to temp dir
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        # Init at second cheat (partial_proof)
        result = await hol_cursor_init(
            file=str(test_file),
            session="cursor_test",
            start_at="partial_proof"
        )
        assert "partial_proof" in result
        assert "Proving partial_proof" in result
        # Should show goals
        assert "goal" in result.lower() or "+" in result
    finally:
        await hol_stop(session="cursor_test")


async def test_cursor_status_shows_cheats(tmp_path):
    """Test hol_cursor_status lists all cheats."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_cursor_init(file=str(test_file), session="status_test")
        result = await hol_cursor_status(session="status_test")

        # Should list both cheats
        assert "needs_proof" in result
        assert "partial_proof" in result
        # Should show line numbers
        assert "line" in result.lower()
        # Should show current marker
        assert "<--" in result
    finally:
        await hol_stop(session="status_test")


async def test_cursor_goto(tmp_path):
    """Test hol_cursor_goto jumps between theorems."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        # Init at first cheat
        await hol_cursor_init(file=str(test_file), session="goto_test")

        # Jump to second cheat
        result = await hol_cursor_goto(session="goto_test", theorem_name="partial_proof")
        assert "Jumped to partial_proof" in result
        assert "goal" in result.lower() or "+" in result

        # Jump back to first
        result = await hol_cursor_goto(session="goto_test", theorem_name="needs_proof")
        assert "Jumped to needs_proof" in result

        # Non-existent theorem
        result = await hol_cursor_goto(session="goto_test", theorem_name="nonexistent")
        assert "ERROR" in result
        assert "not found" in result
        assert "Available cheats:" in result
    finally:
        await hol_stop(session="goto_test")


async def test_cursor_goto_loads_context(tmp_path):
    """Test that goto loads context (earlier theorems) when jumping forward."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        # Init at first cheat (needs_proof at line 18)
        await hol_cursor_init(file=str(test_file), session="ctx_test")

        # Jump to second cheat (partial_proof at line 25)
        # This should load add_zero theorem (lines 11-15) into context
        await hol_cursor_goto(session="ctx_test", theorem_name="partial_proof")

        # Verify add_zero is available in HOL context
        result = await hol_send(session="ctx_test", command="add_zero;", timeout=10)
        # Should return the theorem, not an error
        assert "⊢" in result or "thm" in result.lower()
        assert "not found" not in result.lower()
        assert "error" not in result.lower()
    finally:
        await hol_stop(session="ctx_test")
