"""Tests for HOL file parser."""

import pytest
from pathlib import Path

from hol_file_parser import (
    parse_theorems, parse_file, splice_into_theorem, parse_p_output,
    _parse_tactics_before_cheat,
)

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


def test_parse_p_output_error():
    """Error output should return None, not be spliced as tactics."""
    error_output = """No goalstack is currently being managed.
Exception- HOL_ERR at proofManagerLib.p: raised"""
    assert parse_p_output(error_output) is None
