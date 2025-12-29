"""Tests for HOL proof cursor."""

import pytest
import shutil
import tempfile
import time
from pathlib import Path
from unittest.mock import AsyncMock, Mock

from hol_cursor import ProofCursor, atomic_write, get_executable_content, get_script_dependencies
from hol_file_parser import TheoremInfo
from hol_session import HOLSession

FIXTURES_DIR = Path(__file__).parent / "fixtures"


def test_proof_cursor_next_cheat():
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = [
        TheoremInfo("a", "Theorem", "P", 1, 3, 5, False, [], []),
        TheoremInfo("b", "Theorem", "Q", 10, 12, 14, True, [], []),
        TheoremInfo("c", "Theorem", "R", 20, 22, 24, True, [], []),
    ]
    cursor.position = 0
    cursor.completed = {"b"}
    assert cursor.next_cheat().name == "c"


def test_proof_cursor_goto():
    """Test ProofCursor.goto jumps to theorem by name."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = [
        TheoremInfo("a", "Theorem", "P", 1, 3, 5, False, [], []),
        TheoremInfo("b", "Theorem", "Q", 10, 12, 14, True, [], []),
        TheoremInfo("c", "Theorem", "R", 20, 22, 24, True, [], []),
    ]
    cursor.position = 0

    # Jump to c
    thm = cursor.goto("c")
    assert thm.name == "c"
    assert cursor.position == 2

    # Jump back to a
    thm = cursor.goto("a")
    assert thm.name == "a"
    assert cursor.position == 0

    # Non-existent returns None
    assert cursor.goto("nonexistent") is None
    assert cursor.position == 0  # unchanged


def test_proof_cursor_status_cheats():
    """Test ProofCursor.status includes all cheats with positions."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = [
        TheoremInfo("a", "Theorem", "P", 1, 3, 5, False, [], []),
        TheoremInfo("b", "Theorem", "Q", 10, 12, 14, True, [], []),
        TheoremInfo("c", "Theorem", "R", 20, 22, 24, True, [], []),
        TheoremInfo("d", "Theorem", "S", 30, 32, 34, True, [], []),
    ]
    cursor.position = 1  # at b
    cursor.completed = {"c"}

    status = cursor.status
    assert status["current"] == "b"
    assert status["cheats"] == [
        {"name": "b", "line": 10},
        {"name": "d", "line": 30},
    ]  # c excluded (completed), a excluded (no cheat)


def test_atomic_write():
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "test.txt"
        atomic_write(p, "hello")
        assert p.read_text() == "hello"


def test_get_executable_content_raw_sml():
    """Test get_executable_content with raw SML file (no Theory header)."""
    content = '''(* Comment *)
open HolKernel boolLib;

Definition foo_def:
  foo x = x + 1
End

Theorem bar:
  foo 0 = 1
Proof
  rw[foo_def]
QED
'''
    # Get content up to line 8 (before Theorem bar on line 8)
    result = get_executable_content(content, 8)
    assert "open HolKernel" in result
    assert "Definition foo_def" in result
    assert "Theorem bar" not in result


def test_get_executable_content_script_format():
    """Test get_executable_content skips Theory/Ancestors header."""
    content = '''Theory myTheory
Ancestors
  listTheory arithmeticTheory

(* First executable content *)
Definition foo_def:
  foo x = x + 1
End

Theorem bar:
  foo 0 = 1
Proof
  cheat
QED
'''
    # Get content up to line 11 (Theorem bar)
    result = get_executable_content(content, 11)
    assert "Theory myTheory" not in result
    assert "Ancestors" not in result
    assert "listTheory" not in result
    assert "(* First executable content *)" in result
    assert "Definition foo_def" in result


def test_get_executable_content_multiline_ancestors():
    """Test get_executable_content with multi-line Ancestors."""
    content = '''Theory bigTheory
Ancestors
  list rich_list
  arithmetic prim_rec
  set pred_set

(* Start here *)
val x = 1;
'''
    result = get_executable_content(content, 10)
    assert "Theory" not in result
    assert "Ancestors" not in result
    assert "list rich_list" not in result
    assert "(* Start here *)" in result


@pytest.mark.asyncio
async def test_get_script_dependencies():
    """Test get_script_dependencies with fixture file."""
    fixture = FIXTURES_DIR / "testScript.sml"
    if not fixture.exists():
        pytest.skip("Fixture not found")

    deps = await get_script_dependencies(fixture)
    # Should return list of dependencies
    assert isinstance(deps, list)
    # Basic HOL deps should be present
    assert any("HolKernel" in d or "boolLib" in d for d in deps)


# =============================================================================
# ProofCursor Integration Tests (require HOL)
# =============================================================================

async def test_proof_cursor_initialize():
    """Test ProofCursor.initialize with real HOL session."""
    with tempfile.TemporaryDirectory() as d:
        # Copy fixture to temp dir (so we don't modify original)
        test_file = Path(d) / "testScript.sml"
        shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            result = await cursor.initialize()

            # Should position at first cheat (needs_proof)
            assert "needs_proof" in result
            assert cursor.current().name == "needs_proof"
            assert cursor.current().has_cheat


async def test_proof_cursor_start_current():
    """Test ProofCursor.start_current sets up goaltree."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            result = await cursor.start_current()
            assert "Ready" in result or "needs_proof" in result

            # Verify goaltree is active
            state = await session.send("top_goals();", timeout=10)
            assert "goal" in state.lower() or "+" in state  # Goals present


def test_check_stale_detects_modification():
    """Test _check_stale detects external file modifications."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "test.sml"
        test_file.write_text("original content")

        session = Mock()
        cursor = ProofCursor(test_file, session)
        cursor._file_mtime = test_file.stat().st_mtime

        # Not stale initially
        assert not cursor._check_stale()

        # Modify file
        time.sleep(0.01)  # Ensure mtime changes
        test_file.write_text("modified content")

        # Now stale
        assert cursor._check_stale()


def test_check_stale_missing_file():
    """Test _check_stale returns True for missing file."""
    session = Mock()
    cursor = ProofCursor(Path("/nonexistent/file.sml"), session)
    cursor._file_mtime = 12345.0
    assert cursor._check_stale()


@pytest.mark.asyncio
async def test_complete_and_advance_fails_when_stale():
    """Test complete_and_advance refuses to splice if file was modified."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "test.sml"
        test_file.write_text("""
Theorem foo:
  T
Proof
  cheat
QED
""")
        # Mock session that returns a valid proof
        session = Mock()
        session.send = AsyncMock(return_value="strip_tac\nval it = () : unit")

        cursor = ProofCursor(test_file, session)
        cursor._file_mtime = test_file.stat().st_mtime
        cursor.theorems = [
            TheoremInfo("foo", "Theorem", "T", 2, 4, 6, True, [], []),
        ]
        cursor.position = 0

        # Modify file externally
        time.sleep(0.01)
        test_file.write_text("modified content")

        # complete_and_advance should fail
        result = await cursor.complete_and_advance()
        assert "ERROR" in result
        assert "modified" in result.lower()
        assert "foo" in result  # mentions the theorem


@pytest.mark.asyncio
async def test_complete_and_advance_rejects_error_output():
    """Test complete_and_advance doesn't splice p() error output into file."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        original = """open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
"""
        test_file.write_text(original)

        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Agent abandons the proof
            await session.send("drop();")

            # Now complete_and_advance calls p() which errors
            result = await cursor.complete_and_advance()

            # Should return error, not splice
            assert "ERROR" in result
            assert "No proof found" in result

            # File should be unchanged
            assert test_file.read_text() == original
