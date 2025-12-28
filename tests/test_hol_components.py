"""Tests for HOL agent loop components."""

import pytest
from pathlib import Path

import tempfile
from unittest.mock import Mock

from hol_file_parser import (
    parse_theorems, parse_file, splice_into_theorem, parse_p_output,
    _parse_tactics_before_cheat, TheoremInfo,
)
from hol_cursor import ProofCursor, atomic_write, get_executable_content, get_script_dependencies
from hol_session import HOLSession
from hol_proof_agent import is_allowed_command, get_large_files

FIXTURES_DIR = Path(__file__).parent / "fixtures"


def test_parse_theorems():
    """Test parsing theorems from content."""
    content = r'''
Theorem foo[simp]:
  !x. P x ==> Q x
Proof
  rw[] \\
  cheat
QED

Triviality bar:
  A /\ B ==> B /\ A
Proof
  metis_tac[]
QED

Theorem baz[local,simp]:
  !n. n + 0 = n
Proof
  Induct_on `n` \\
  gvs[] \\
  cheat
QED
'''
    thms = parse_theorems(content)

    assert len(thms) == 3

    assert thms[0].name == "foo"
    assert thms[0].kind == "Theorem"
    assert thms[0].has_cheat == True
    assert thms[0].attributes == ["simp"]
    assert len(thms[0].tactics_before_cheat) >= 1

    assert thms[1].name == "bar"
    assert thms[1].kind == "Triviality"
    assert thms[1].has_cheat == False

    assert thms[2].name == "baz"
    assert thms[2].attributes == ["local", "simp"]
    assert thms[2].has_cheat == True


def test_parse_fixture_file():
    """Test parsing the fixture HOL file."""
    f = FIXTURES_DIR / "testScript.sml"
    if not f.exists():
        pytest.skip(f"Fixture not found: {f}")

    thms = parse_file(f)
    assert len(thms) == 5

    assert thms[0].name == "add_zero"
    assert thms[0].has_cheat == False

    assert thms[1].name == "needs_proof"
    assert thms[1].has_cheat == True

    assert thms[2].name == "partial_proof"
    assert thms[2].has_cheat == True
    assert len(thms[2].tactics_before_cheat) >= 1

    assert thms[4].name == "helper_lemma"
    assert thms[4].kind == "Triviality"


def test_splice_into_theorem():
    """Test splicing proof into theorem."""
    content = '''Theorem foo:
  !x. P x
Proof
  cheat
QED

Theorem bar:
  A
Proof
  simp[]
QED
'''
    new = splice_into_theorem(content, 'foo', 'Induct_on `x` \\\\ gvs[]')

    assert 'Induct_on `x`' in new
    assert 'cheat' not in new.split('Theorem bar')[0]
    assert 'simp[]' in new


def test_parse_p_output():
    """Test parsing p() output."""
    output = '''> p();
Induct_on `x` \\
gvs[] \\
simp[foo_def]
val it = () : unit
'''
    result = parse_p_output(output)
    assert result == '''Induct_on `x` \\
gvs[] \\
simp[foo_def]'''


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


def test_is_allowed_command():
    """Test bash command allowlist validation."""
    # Should allow - git only
    assert is_allowed_command('git add foo.py')
    assert is_allowed_command('git commit -m "msg"')
    assert is_allowed_command('git status')
    assert is_allowed_command('git diff')
    assert is_allowed_command('git log --oneline')

    # Should block - use holmake MCP tool instead
    assert not is_allowed_command('Holmake')
    assert not is_allowed_command('FOO=/path Holmake')

    # Should block - dangerous commands
    assert not is_allowed_command('rm -rf /')
    assert not is_allowed_command('git add; rm -rf /')  # semicolon chain
    assert not is_allowed_command('git add && rm -rf /')  # && chain
    assert not is_allowed_command('git add | cat')  # pipe
    assert not is_allowed_command('git push')  # not in allowlist
    assert not is_allowed_command('cat /etc/passwd')
    assert not is_allowed_command('')
    assert not is_allowed_command('git')  # bare git
    assert not is_allowed_command('echo $(whoami)')  # command substitution


# =============================================================================
# File Parser Tests (_parse_tactics_before_cheat, _indent)
# =============================================================================

def test_parse_tactics_before_cheat_basic():
    result = _parse_tactics_before_cheat("rw[] \\\\ cheat")
    assert result == ["rw[]"]


def test_parse_tactics_before_cheat_multiple():
    result = _parse_tactics_before_cheat("rw[] \\\\ gvs[] \\\\ cheat")
    assert result == ["rw[]", "gvs[]"]


def test_parse_tactics_before_cheat_nested_parens():
    result = _parse_tactics_before_cheat("(rw[] \\\\ gvs[]) \\\\ cheat")
    assert result == ["(rw[] \\\\ gvs[])"]


def test_parse_tactics_before_cheat_subgoal():
    result = _parse_tactics_before_cheat("rw[] >- gvs[] \\\\ cheat")
    assert result == ["rw[]", "gvs[]"]


def test_parse_tactics_before_cheat_empty():
    assert _parse_tactics_before_cheat("cheat") == []


def test_parse_tactics_before_cheat_no_cheat():
    assert _parse_tactics_before_cheat("rw[]") == []


def test_splice_into_theorem_not_found():
    content = 'Theorem foo:\n  P\nProof\n  cheat\nQED\n'
    with pytest.raises(ValueError, match="not found"):
        splice_into_theorem(content, 'nonexistent', 'simp[]')


def test_parse_p_output_empty():
    assert parse_p_output("") is None


def test_parse_p_output_only_prompts():
    assert parse_p_output("> p();\nval it = () : unit\n") is None


# =============================================================================
# Cursor Navigation Tests (ProofCursor, atomic_write)
# =============================================================================

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


def test_atomic_write():
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "test.txt"
        atomic_write(p, "hello")
        assert p.read_text() == "hello"


# =============================================================================
# Agent Helpers Tests (get_large_files)
# =============================================================================

def test_get_large_files_empty():
    with tempfile.TemporaryDirectory() as d:
        assert get_large_files(d) == []


def test_get_large_files_finds_large():
    with tempfile.TemporaryDirectory() as d:
        small = Path(d) / "small.sml"
        small.write_text("x\n" * 100)
        large = Path(d) / "large.sml"
        # Need 600 lines AND >= byte_threshold (default 15000 bytes).
        # "x" * 30 + "\n" = 31 bytes per line, 600 lines = 18600 bytes > 15000
        large.write_text(("x" * 30 + "\n") * 600)
        result = get_large_files(d, line_threshold=500)
        assert len(result) == 1
        assert result[0][0] == "large.sml"
        assert result[0][1] == 600


# =============================================================================
# ProofCursor Integration Tests
# =============================================================================

async def test_proof_cursor_initialize():
    """Test ProofCursor.initialize with real HOL session."""
    import shutil
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
    import shutil
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
# Session Edge Case Tests
# =============================================================================

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


