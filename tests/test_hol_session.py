"""Tests for HOL session subprocess wrapper."""

import pytest
from pathlib import Path

from hol_session import HOLSession, escape_sml_string
from hol_cursor import _is_hol_error, _parse_sml_string

FIXTURES_DIR = Path(__file__).parent / "fixtures"


async def test_hol_session():
    """Test HOL session basic functionality."""
    session = HOLSession(str(FIXTURES_DIR))
    try:
        result = await session.start()
        assert "HOL started" in result

        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result

        assert session.is_running
    finally:
        await session.stop()
        assert not session.is_running


async def test_hol_session_context_manager():
    """Test HOL session as async context manager."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        assert session.is_running
        result = await session.send('3 + 4;', timeout=10)
        assert "7" in result
        assert session.is_running
    assert not session.is_running


async def test_hol_session_interrupt():
    """Test interrupting a long-running HOL command."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Start a long-running computation via short timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should still be usable after interrupt
        assert session.is_running
        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result


async def test_hol_session_send_not_running():
    """Test sending to a stopped session returns error."""
    session = HOLSession(str(FIXTURES_DIR))
    result = await session.send('1 + 1;', timeout=10)
    assert "ERROR" in result


async def test_hol_session_start_already_running():
    async with HOLSession(str(FIXTURES_DIR)) as session:
        pid = session.process.pid
        result = await session.start()
        assert "already running" in result.lower()
        assert session.process.pid == pid


async def test_hol_session_sequential_sends():
    """Test sequential sends return correct outputs in order."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        for i in range(10):
            result = await session.send(f'{i};', timeout=10)
            assert str(i) in result, f"Expected {i} in result, got: {result}"


async def test_hol_session_post_interrupt_sync():
    """Test that session resyncs correctly after interrupt.

    After timeout/interrupt, buffer and pipe may have stale data.
    Verify subsequent commands work correctly.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Trigger interrupt with a timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should resync - send a few commands and verify correct outputs
        for i in range(5):
            result = await session.send(f'{100 + i};', timeout=10)
            assert str(100 + i) in result, f"Expected {100+i} after interrupt, got: {result}"


# Unit tests for escape_sml_string

def test_escape_sml_string_backslash():
    """Backslash should be doubled for SML string literal."""
    assert escape_sml_string('/\\') == '/\\\\'
    assert escape_sml_string('A /\\ B') == 'A /\\\\ B'


def test_escape_sml_string_quote():
    """Double quotes should be escaped."""
    assert escape_sml_string('SPEC "x"') == 'SPEC \\"x\\"'


def test_escape_sml_string_newline():
    """Newlines should become \\n."""
    assert escape_sml_string('foo\nbar') == 'foo\\nbar'


def test_escape_sml_string_tab():
    """Tabs should become \\t."""
    assert escape_sml_string('foo\tbar') == 'foo\\tbar'


def test_escape_sml_string_carriage_return():
    """Carriage returns should become \\r."""
    assert escape_sml_string('foo\rbar') == 'foo\\rbar'


def test_escape_sml_string_combined():
    """Test multiple escape sequences together."""
    # /\ with newline and embedded quote
    assert escape_sml_string('`T /\\ T`\nby SPEC "x"') == '`T /\\\\ T`\\nby SPEC \\"x\\"'


def test_escape_sml_string_no_change():
    """Regular strings pass through unchanged."""
    assert escape_sml_string('simp[]') == 'simp[]'
    assert escape_sml_string('strip_tac') == 'strip_tac'


# Tests for _is_hol_error with real HOL output

async def test_is_hol_error_detects_syntax_error():
    """Poly/ML syntax errors should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('val x = ;', timeout=10)  # syntax error
        assert _is_hol_error(result), f"Should detect syntax error: {result}"


async def test_is_hol_error_detects_type_error():
    """Poly/ML type errors should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('val x : int = "hello";', timeout=10)
        assert _is_hol_error(result), f"Should detect type error: {result}"


async def test_is_hol_error_detects_exception():
    """SML exceptions should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('raise Fail "test";', timeout=10)
        assert _is_hol_error(result), f"Should detect exception: {result}"


async def test_is_hol_error_ignores_error_in_term():
    """The word 'error' in a term should NOT trigger error detection."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Define a value with "error" in the name - this is valid SML
        result = await session.send('val error_state = 42;', timeout=10)
        assert not _is_hol_error(result), f"Should not flag 'error' in identifier: {result}"

        # Use "error" in a HOL term
        result = await session.send('val t = ``is_error x``;', timeout=10)
        assert not _is_hol_error(result), f"Should not flag 'error' in term: {result}"


def test_is_hol_error_detects_timeout():
    """_is_hol_error catches TIMEOUT strings from send()."""
    assert _is_hol_error("TIMEOUT after 30s - sent interrupt.")
    assert _is_hol_error("TIMEOUT after 5s - sent interrupt.\npartial output")


def test_is_hol_error_detects_error_prefix():
    """_is_hol_error catches ERROR: sentinel outputs."""
    assert _is_hol_error("ERROR: HOL not running")
    assert _is_hol_error("Error: HOL not running")


def test_parse_sml_string_with_space():
    """_parse_sml_string handles space before colon."""
    # No space before colon
    assert _parse_sml_string('val it = "hello": string') == "hello"
    # Space before colon (Poly/ML format)
    assert _parse_sml_string('val it = "hello" : string') == "hello"
    # With escapes
    assert _parse_sml_string('val it = "a\\\\b": string') == "a\\\\b"


# =============================================================================
# Pipe communication bug reproduction tests
# =============================================================================


async def test_open_shows_bindings():
    """Verify that 'open' statements show theorem bindings (file-based execution).

    With file-based execution (QUse.use), open shows all bindings brought into scope.
    This is actually more informative for agents.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('open boolTheory;', timeout=10)
        # File-based execution shows bindings from open
        assert "TRUTH" in result, f"Expected theorem bindings, got: {repr(result)}"
        assert "thm" in result, f"Expected 'thm' type annotations, got: {repr(result)}"


async def test_load_then_open_sequence():
    """Verify load followed by open both work correctly.

    Tests that file-based execution handles both commands properly:
    1. load "Theory"; -> completes without error
    2. open Theory;   -> shows bindings
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Step 1: load produces output (may or may not have "unit" with file-based)
        result1 = await session.send('load "bossLib";', timeout=30)
        assert "error" not in result1.lower(), f"load failed: {repr(result1)}"

        # Step 2: open shows bindings with file-based execution
        result2 = await session.send('open boolTheory;', timeout=10)
        # Verify we get theorem bindings, not garbage or error
        assert "thm" in result2, f"open should show bindings, got: {repr(result2)}"

        # Step 3: verify session still works correctly
        result3 = await session.send('1 + 1;', timeout=10)
        assert "2" in result3, f"Expected 2, got: {repr(result3)}"


async def test_output_then_no_output_rapid():
    """Test rapid alternation between commands with/without output.

    If there's a race in _drain_pipe(), rapid sequences might expose it.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        for i in range(20):
            # Command with output
            result = await session.send(f'{i};', timeout=10)
            assert str(i) in result, f"Iteration {i}: expected {i} in result, got: {repr(result)}"

            # Command with no output (val _ = ... produces no output)
            result = await session.send(f'val _ = {i};', timeout=10)
            # val _ binding produces no output
            assert result == "", f"Iteration {i}: val _ should be empty, got: {repr(result)}"


async def test_multiple_opens_then_command():
    """Test multiple opens followed by a computation.

    With file-based execution, opens show bindings. Verify session continues working.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Multiple opens (show bindings with file-based execution)
        for theory in ['boolTheory', 'numTheory', 'listTheory']:
            result = await session.send(f'open {theory};', timeout=10)
            assert "thm" in result or "val" in result, f"open {theory} should show bindings: {repr(result)[:100]}"

        # Now a command that should return output
        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result, f"After opens, expected 2, got: {repr(result)}"


async def test_slow_command_then_fast_command():
    """Test if slow command followed by fast command causes response mixup.

    If _drain_pipe races with late-arriving data, we might get wrong response.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Slow command (computation)
        result1 = await session.send('val slow = List.tabulate(10000, fn i => i);', timeout=30)
        # Should contain something about the list
        assert "int list" in result1 or "val slow" in result1, f"Slow cmd result: {repr(result1)}"

        # Immediate fast command
        result2 = await session.send('42;', timeout=10)
        assert "42" in result2, f"Fast cmd after slow: expected 42, got: {repr(result2)}"
        # Make sure we didn't get leftover from slow command
        assert "10000" not in result2, f"Got leftover from slow cmd: {repr(result2)}"


# =============================================================================
# Prolonged use test - single session through many operations
# =============================================================================


async def test_static_error_recovery():
    """Verify session survives static errors (file-based execution fix).

    Previously (stdin), static errors would corrupt the session. With file-based
    execution, static errors become runtime exceptions that the REPL handles.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Normal command works
        result = await session.send('1;', timeout=10)
        assert "1" in result, f"Before error: expected 1, got {repr(result)}"

        # Trigger an error (open non-loaded theory)
        result = await session.send('open NonExistentFooTheory;', timeout=10)
        assert "error" in result.lower(), f"Should be error: {repr(result)}"

        # BUG: After error, commands return empty
        result = await session.send('2;', timeout=10)
        assert "2" in result, f"After error: expected 2, got {repr(result)}"

        result = await session.send('3;', timeout=10)
        assert "3" in result, f"Second after error: expected 3, got {repr(result)}"


async def test_prolonged_session_use():
    """Simulate prolonged use: single session through many diverse operations.

    Tests for state corruption that accumulates over time.
    Includes: basic commands, opens, loads, goaltree, interrupts, stress.
    """
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    failures = []

    try:
        # Phase 1: Basic commands
        for i in range(20):
            result = await session.send(f'{i};', timeout=10)
            if str(i) not in result:
                failures.append(f"Phase1 i={i}: expected {i}, got {repr(result)}")

        # Phase 2: Opens (shows bindings with file-based execution)
        for theory in ['boolTheory', 'numTheory', 'listTheory']:
            result = await session.send(f'open {theory};', timeout=10)
            if "thm" not in result and "val" not in result:
                failures.append(f"Phase2 open {theory}: expected bindings, got {repr(result)[:100]}")

        result = await session.send('100;', timeout=10)
        if "100" not in result:
            failures.append(f"Phase2 after opens: expected 100, got {repr(result)}")

        # Phase 3: Load then open (both show output with file-based execution)
        result = await session.send('load "bossLib";', timeout=30)
        if "error" in result.lower():
            failures.append(f"Phase3 load failed: {repr(result)[:100]}")

        result = await session.send('open pairTheory;', timeout=10)
        if "thm" not in result and "val" not in result:
            failures.append(f"Phase3 open after load: expected bindings, got {repr(result)[:100]}")

        result = await session.send('200;', timeout=10)
        if "200" not in result:
            failures.append(f"Phase3 after load+open: expected 200, got {repr(result)}")

        # Phase 4: Goaltree mode
        result = await session.send('gt `1 + 1 = 2`;', timeout=10)
        # Just check it doesn't error
        result = await session.send('etq "EVAL_TAC";', timeout=10)
        result = await session.send('drop();', timeout=10)

        result = await session.send('300;', timeout=10)
        if "300" not in result:
            failures.append(f"Phase4 after goaltree: expected 300, got {repr(result)}")

        # Phase 5: Trigger interrupt
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        if "TIMEOUT" not in result and "interrupt" not in result.lower():
            failures.append(f"Phase5 interrupt: expected timeout, got {repr(result)}")

        result = await session.send('400;', timeout=10)
        if "400" not in result:
            failures.append(f"Phase5 after interrupt: expected 400, got {repr(result)}")

        # Phase 6: Stress after interrupt
        for i in range(50):
            result = await session.send(f'{500 + i};', timeout=10)
            if str(500 + i) not in result:
                failures.append(f"Phase6 i={i}: expected {500+i}, got {repr(result)}")

        # Phase 7: Mixed after stress
        result = await session.send('open optionTheory;', timeout=10)
        if "thm" not in result and "val" not in result:
            failures.append(f"Phase7 late open: expected bindings, got {repr(result)[:100]}")

        result = await session.send('600;', timeout=10)
        if "600" not in result:
            failures.append(f"Phase7 after open: expected 600, got {repr(result)}")

        # Use combinTheory which is part of bossLib
        result = await session.send('open combinTheory;', timeout=10)
        if "thm" not in result and "val" not in result:
            failures.append(f"Phase7 late open 2: expected bindings, got {repr(result)[:100]}")

        result = await session.send('700;', timeout=10)
        if "700" not in result:
            failures.append(f"Phase7 after open 2: expected 700, got {repr(result)}")

        # Phase 8: Final stress - alternating output/no-output
        for i in range(100):
            result = await session.send(f'{800 + i};', timeout=10)
            if str(800 + i) not in result:
                failures.append(f"Phase8 i={i} output: expected {800+i}, got {repr(result)}")

            result = await session.send(f'val _ = {i};', timeout=10)
            if result != "":
                failures.append(f"Phase8 i={i} no-output: expected empty, got {repr(result)}")

        # Phase 9: Multiple interrupts
        for j in range(3):
            result = await session.send('fun loop () = loop (); loop ();', timeout=1)
            result = await session.send(f'{1000 + j};', timeout=10)
            if str(1000 + j) not in result:
                failures.append(f"Phase9 post-interrupt {j}: expected {1000+j}, got {repr(result)}")

        # Phase 10: Final verification
        for i in range(20):
            result = await session.send(f'{2000 + i};', timeout=10)
            if str(2000 + i) not in result:
                failures.append(f"Phase10 final i={i}: expected {2000+i}, got {repr(result)}")

    finally:
        await session.stop()

    assert not failures, f"Prolonged session failures ({len(failures)}):\n" + "\n".join(failures[:20])
