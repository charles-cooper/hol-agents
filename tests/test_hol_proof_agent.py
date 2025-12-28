"""Tests for HOL proof agent helpers."""

import tempfile
from pathlib import Path

from hol_proof_agent import is_allowed_command, get_large_files


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
