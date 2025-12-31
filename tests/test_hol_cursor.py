"""Tests for HOL proof cursor."""

import pytest
import shutil
import tempfile
from pathlib import Path
from unittest.mock import AsyncMock, Mock

from hol_cursor import ProofCursor, get_executable_content, get_script_dependencies
from hol_file_parser import TheoremInfo
from hol_session import HOLSession

FIXTURES_DIR = Path(__file__).parent / "fixtures"


@pytest.fixture
def mock_theorems():
    """Common TheoremInfo list for cursor unit tests."""
    return [
        TheoremInfo("a", "Theorem", "P", 1, 3, 5, False),
        TheoremInfo("b", "Theorem", "Q", 10, 12, 14, True),
        TheoremInfo("c", "Theorem", "R", 20, 22, 24, True),
    ]


def test_proof_cursor_next_cheat(mock_theorems):
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
    cursor.position = 0
    cursor.completed = {"b"}
    assert cursor.next_cheat().name == "c"


def test_next_cheat_finds_earlier_theorem(mock_theorems):
    """Test next_cheat finds cheats earlier in file, not just forward."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
    # Position at end of file, but first cheat (b) is earlier
    cursor.position = 2
    cursor.completed = {"c"}  # Last theorem completed

    # Should find b even though it's before current position
    thm = cursor.next_cheat()
    assert thm is not None
    assert thm.name == "b"
    assert cursor.position == 1


def test_next_cheat_returns_none_when_all_done(mock_theorems):
    """Test next_cheat returns None when all cheats are completed."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
    cursor.position = 2
    cursor.completed = {"b", "c"}  # All cheats done

    assert cursor.next_cheat() is None


def test_proof_cursor_goto(mock_theorems):
    """Test ProofCursor.goto jumps to theorem by name."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
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


def test_proof_cursor_status_cheats(mock_theorems):
    """Test ProofCursor.status includes all cheats with positions."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems + [TheoremInfo("d", "Theorem", "S", 30, 32, 34, True)]
    cursor.position = 1  # at b
    cursor.completed = {"c"}

    status = cursor.status
    assert status["current"] == "b"
    assert status["cheats"] == [
        {"name": "b", "line": 10},
        {"name": "d", "line": 30},
    ]  # c excluded (completed), a excluded (no cheat)


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
    """Test get_executable_content includes Theory/Ancestors header."""
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
    # Get content up to line 10 (Theorem bar starts on line 10)
    result = get_executable_content(content, 10)
    # Header is now included (sets up environment)
    assert "Theory myTheory" in result
    assert "Ancestors" in result
    assert "listTheory" in result
    assert "(* First executable content *)" in result
    assert "Definition foo_def" in result
    # But not the theorem we're about to prove
    assert "Theorem bar" not in result


def test_get_executable_content_multiline_ancestors():
    """Test get_executable_content includes multi-line Ancestors header."""
    content = '''Theory bigTheory
Ancestors
  list rich_list
  arithmetic prim_rec
  set pred_set

(* Start here *)
val x = 1;
'''
    result = get_executable_content(content, 10)
    # Header is now included (sets up environment)
    assert "Theory" in result
    assert "Ancestors" in result
    assert "list rich_list" in result
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


@pytest.mark.asyncio
async def test_complete_and_advance_rejects_error_output():
    """Test complete_and_advance returns error when p() fails."""
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

            # Should return error dict
            assert "error" in result
            assert "No proof found" in result["error"]


@pytest.mark.asyncio
async def test_complete_and_advance_rejects_anonymous():
    """Test complete_and_advance rejects proofs with <anonymous> tactics."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Use e() instead of etq - loses tactic name
            await session.send("e(REWRITE_TAC[]);")

            result = await cursor.complete_and_advance()

            assert "error" in result
            assert "anonymous" in result["error"].lower()


@pytest.mark.asyncio
async def test_complete_and_advance_returns_proof():
    """Test complete_and_advance returns proof dict on success."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Complete the proof properly
            await session.send('etq "REWRITE_TAC[]";')

            result = await cursor.complete_and_advance()

            # Should return proof dict
            assert "error" not in result
            assert result["theorem"] == "foo"
            assert "proof" in result
            assert result["next_cheat"] is None  # only one theorem


@pytest.mark.asyncio
async def test_tactics_before_cheat_subgoal_replay():
    """Test that >- structured tactics replay correctly."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # A proof with >- structure
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem conj_swap:
  A /\\ B ==> B /\\ A
Proof
  strip_tac >- simp[] \\\\
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Check what tactics were parsed
            thm = cursor.current()
            assert thm.name == "conj_swap"

            # Start current replays tactics
            result = await cursor.start_current()

            # Check the goaltree state after replay
            p_output = await session.send("p();")

            # The key question: does p() show the original structure?
            # If we split on >-, the structure will be wrong
            print(f"Proof body: {thm.proof_body}")
            print(f"p() output: {p_output}")

            # Verify >- is preserved (not converted to \\)
            assert ">-" in p_output, f"Expected >- in output, got: {p_output}"


@pytest.mark.asyncio
async def test_cheat_finder_no_exhaustivity_warnings():
    """Test that cheat_finder.sml loads without pattern match warnings."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Session start loads cheat_finder.sml - check no warnings in output
            # by re-loading and checking output
            cheat_finder = Path(__file__).parent.parent / "sml_helpers" / "cheat_finder.sml"
            result = await session.send(cheat_finder.read_text(), timeout=30)
            # Poly/ML warnings contain "Warning:" for non-exhaustive matches
            assert "Warning" not in result, f"Got warnings: {result}"
            assert "warning" not in result.lower() or "dropWhile" in result, f"Got warnings: {result}"


@pytest.mark.asyncio
async def test_extract_before_cheat_edge_cases():
    """Test extract_before_cheat handles various edge cases."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            async def extract(s: str) -> str:
                escaped = s.replace("\\", "\\\\").replace('"', '\\"')
                result = await session.send(f'extract_before_cheat "{escaped}";')
                # Parse val it = "...": string
                for line in result.split('\n'):
                    if 'val it = "' in line and '": string' in line:
                        start = line.index('"') + 1
                        end = line.rindex('": string')
                        return line[start:end].replace("\\\\", "\\")
                return ""

            # Basic: each operator type
            assert await extract("cheat") == ""
            assert await extract("simp[] \\\\ cheat") == "simp[]"
            assert await extract("simp[] \\\\ CHEAT") == "simp[]"
            assert await extract("strip_tac >> cheat") == "strip_tac"
            assert await extract("rw[] >- cheat") == "rw[]"

            # Multiple cheats - extracts before FIRST
            assert await extract("simp[] \\\\ cheat \\\\ gvs[] \\\\ cheat") == "simp[]"

            # Nested structure
            assert await extract("(strip_tac \\\\ simp[]) \\\\ cheat") == "(strip_tac \\\\ simp[])"

            # Chained subgoals and mixed operators
            assert await extract("conj_tac >- simp[] >- cheat") == "conj_tac >- simp[]"
            assert await extract("a >> b \\\\ c >- d >> cheat") == "a >> b \\\\ c >- d"

            # Empty input
            assert await extract("") == "" and await extract("   ") == ""

            # "cheat" in identifier/backquote (should find real cheat tactic)
            assert await extract("simp[cheat_def] \\\\ cheat") == "simp[cheat_def]"
            assert await extract("foo `cheat` \\\\ cheat") == "foo `cheat`"

            # Embedded quotes (must stay escaped for etq)
            result = await extract('rename1 "x" \\\\ cheat')
            assert 'rename1' in result and 'x' in result

            # Known limitation: SML keywords (if/case/fn) in backquotes break TacticParse
            assert await extract("qexists_tac `if x then y else z` \\\\ cheat") == ""
            assert await extract("foo `case x of _ => y` \\\\ cheat") == ""
            assert await extract("foo `fn x => x` \\\\ cheat") == ""
            assert await extract("qexists_tac `x` \\\\ cheat") == "qexists_tac `x`"  # simple backquote works

            # Test cases for nested structures - should return empty (invalid prefix)
            assert await extract("strip_tac >- (simp[] \\\\ cheat)") == ""
            assert await extract("(a >- b >- cheat)") == ""


@pytest.mark.asyncio
async def test_start_current_with_backslash_tactic():
    """Test tactics with /\\ in terms are escaped properly for etq."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # A proof with /\ in the goal (requires escaping for SML strings)
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem conj_true:
  T /\\ T
Proof
  simp[] \\\\
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Check theorem was found
            thm = cursor.current()
            assert thm.name == "conj_true"

            # start_current should work - the /\ in the goal needs escaping
            result = await cursor.start_current()

            # Should not error - if escaping fails, we'd see an SML parse error
            assert "ERROR" not in result
            assert "Ready" in result or "conj_true" in result

            # Verify the pre-cheat tactic was replayed
            p_output = await session.send("p();")
            assert "simp" in p_output


@pytest.mark.asyncio
async def test_drop_all_clears_stacked_goaltrees():
    """Test drop_all() clears all stacked goaltrees."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Stack multiple goaltrees
            await session.send('gt `A ==> A`;')
            await session.send('gt `B ==> B`;')
            await session.send('gt `C ==> C`;')

            # Verify 3 proofs on stack
            status = await session.send('status();')
            assert "3 proofs" in status

            # drop_all should clear everything
            result = await session.send('drop_all();')
            assert "no proofs" in result.lower()

            # Verify empty
            status = await session.send('status();')
            assert "no proofs" in status.lower()

            # Can start fresh
            await session.send('gt `X ==> X`;')
            status = await session.send('status();')
            assert "1 proof" in status


@pytest.mark.asyncio
async def test_drop_all_idempotent():
    """Test drop_all() is safe to call on empty state."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Call drop_all on empty state - should not error
            result = await session.send('drop_all();')
            assert "no proofs" in result.lower()

            # Call again - still safe
            result = await session.send('drop_all();')
            assert "no proofs" in result.lower()


@pytest.mark.asyncio
async def test_start_current_clears_stacked_proofs():
    """Test start_current() uses drop_all() to clear stacked proofs."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Enter goaltree for foo (like MCP tool does)
            await cursor.start_current()

            # Stack extra goaltrees (simulating agent doing manual gt calls)
            await session.send('gt `A ==> A`;')
            await session.send('gt `B ==> B`;')

            # Verify we have multiple proofs now
            status = await session.send('status();')
            assert "3 proof" in status  # original + 2 extra

            # start_current should clear all and start fresh
            result = await cursor.start_current()
            assert "ERROR" not in result

            # Should have exactly 1 proof now (foo)
            status = await session.send('status();')
            assert "1 proof" in status

            # And it should be the right goal
            goals = await session.send('top_goals();')
            assert "T" in goals


@pytest.mark.asyncio
async def test_complete_and_advance_finds_earlier_cheat():
    """Test complete_and_advance finds cheats earlier in file after completing later one."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # Two theorems with cheats
        test_file.write_text("""open HolKernel boolLib;

Theorem first:
  T
Proof
  cheat
QED

Theorem second:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Jump to second theorem (skipping first)
            cursor.goto("second")
            await cursor.start_current()

            # Complete second theorem
            await session.send('etq "simp[]";')
            result = await cursor.complete_and_advance()

            # Should find "first" as next_cheat (even though it's earlier in file)
            assert "error" not in result
            assert result["theorem"] == "second"
            assert result["next_cheat"]["name"] == "first"


@pytest.mark.asyncio
async def test_complete_and_advance_with_next_cheat():
    """Test complete_and_advance returns next_cheat when more cheats remain."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # Two theorems with cheats
        test_file.write_text("""open HolKernel boolLib;

Theorem first:
  T
Proof
  cheat
QED

Theorem second:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Complete the proof
            await session.send('etq "simp[]";')
            result = await cursor.complete_and_advance()

            # Should return dict with theorem and next_cheat
            assert "error" not in result
            assert result["theorem"] == "first"
            assert result["next_cheat"]["name"] == "second"
            assert "proof" in result


@pytest.mark.asyncio
async def test_start_current_loads_intermediate_context():
    """Test start_current loads definitions between theorems."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # First theorem, then a definition, then second theorem that uses it
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem first:
  T
Proof
  cheat
QED

Definition my_val_def:
  my_val = (5:num)
End

Theorem uses_def:
  my_val = 5
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Complete first theorem
            await session.send('etq "simp[]";')
            result = await cursor.complete_and_advance()
            assert result["next_cheat"]["name"] == "uses_def"

            # Now start_current for uses_def - should load my_val_def
            start_result = await cursor.start_current()
            assert "ERROR" not in start_result

            # Prove using the definition - this would fail if def wasn't loaded
            tac_result = await session.send('etq "simp[my_val_def]";')
            assert "Exception" not in tac_result
            assert "error" not in tac_result.lower()

            # Verify proof completed (empty goal list)
            goals = await session.send("top_goals();")
            assert "[]" in goals  # empty goal list
