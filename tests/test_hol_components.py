"""Tests for HOL agent loop components."""

import pytest
from pathlib import Path

from hol_file_parser import parse_theorems, parse_file, splice_into_theorem, parse_p_output
from hol_session import HOLSession
from hol_proof_agent import is_allowed_command

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

    # Should block - use hol_build MCP tool instead
    assert not is_allowed_command('Holmake')
    assert not is_allowed_command('MYVAR=/path Holmake')

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
