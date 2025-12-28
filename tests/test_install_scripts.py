"""Tests for install.sh and uninstall.sh scripts."""

import json
import os
import subprocess
import tempfile
from pathlib import Path

import pytest

REPO_DIR = Path(__file__).parent.parent


@pytest.fixture
def project_dir():
    """Create a temporary project directory with .claude folder."""
    with tempfile.TemporaryDirectory() as tmpdir:
        claude_dir = Path(tmpdir) / ".claude"
        claude_dir.mkdir()
        yield Path(tmpdir)


def run_install(project_dir, *args):
    """Run install.sh in project directory."""
    return subprocess.run(
        [str(REPO_DIR / "install.sh"), *args],
        cwd=project_dir,
        capture_output=True,
        text=True,
    )


def run_uninstall(project_dir):
    """Run uninstall.sh in project directory."""
    return subprocess.run(
        [str(REPO_DIR / "uninstall.sh")],
        cwd=project_dir,
        capture_output=True,
        text=True,
    )


class TestInstallStdio:
    """Test install.sh with stdio transport (default)."""

    def test_creates_mcp_json(self, project_dir):
        result = run_install(project_dir)
        assert result.returncode == 0

        mcp_json = project_dir / ".mcp.json"
        assert mcp_json.exists()

        config = json.loads(mcp_json.read_text())
        assert "hol" in config["mcpServers"]
        assert config["mcpServers"]["hol"]["command"] == "python3"
        assert "hol_mcp_server.py" in config["mcpServers"]["hol"]["args"][0]

    def test_creates_skills_symlink(self, project_dir):
        result = run_install(project_dir)
        assert result.returncode == 0

        skills_link = project_dir / ".claude" / "skills" / "hol4"
        assert skills_link.is_symlink()
        assert (skills_link / "SKILL.md").exists()

    def test_updates_existing_mcp_json(self, project_dir):
        # Create existing .mcp.json with other server
        mcp_json = project_dir / ".mcp.json"
        mcp_json.write_text(json.dumps({
            "mcpServers": {
                "other": {"command": "other-server"}
            }
        }))

        result = run_install(project_dir)
        assert result.returncode == 0

        config = json.loads(mcp_json.read_text())
        assert "other" in config["mcpServers"]
        assert "hol" in config["mcpServers"]


class TestInstallHttp:
    """Test install.sh with http transport."""

    def test_creates_http_config(self, project_dir):
        result = run_install(project_dir, "--transport", "http")
        assert result.returncode == 0

        mcp_json = project_dir / ".mcp.json"
        config = json.loads(mcp_json.read_text())

        assert config["mcpServers"]["hol"]["type"] == "http"
        assert "localhost:8000" in config["mcpServers"]["hol"]["url"]

    def test_custom_port(self, project_dir):
        result = run_install(project_dir, "--transport", "http", "--port", "9000")
        assert result.returncode == 0

        mcp_json = project_dir / ".mcp.json"
        config = json.loads(mcp_json.read_text())

        assert "localhost:9000" in config["mcpServers"]["hol"]["url"]

    def test_prints_server_start_instructions(self, project_dir):
        result = run_install(project_dir, "--transport", "http")
        assert "Start the server before using Claude Code" in result.stdout


class TestInstallErrors:
    """Test install.sh error handling."""

    def test_invalid_transport(self, project_dir):
        result = run_install(project_dir, "--transport", "invalid")
        assert result.returncode != 0
        assert "must be 'stdio' or 'http'" in result.stderr

    def test_no_claude_dir(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            result = run_install(Path(tmpdir))
            assert result.returncode != 0
            assert "No .claude directory" in result.stderr


class TestUninstall:
    """Test uninstall.sh."""

    def test_removes_hol_server(self, project_dir):
        # Install first
        run_install(project_dir)

        # Uninstall
        result = run_uninstall(project_dir)
        assert result.returncode == 0

        mcp_json = project_dir / ".mcp.json"
        # Should be removed since no other servers
        assert not mcp_json.exists()

    def test_removes_skills_symlink(self, project_dir):
        run_install(project_dir)

        result = run_uninstall(project_dir)
        assert result.returncode == 0

        skills_link = project_dir / ".claude" / "skills" / "hol4"
        assert not skills_link.exists()

    def test_preserves_other_servers(self, project_dir):
        # Create .mcp.json with other server
        mcp_json = project_dir / ".mcp.json"
        mcp_json.write_text(json.dumps({
            "mcpServers": {
                "other": {"command": "other-server"}
            }
        }))

        # Install hol
        run_install(project_dir)

        # Uninstall
        result = run_uninstall(project_dir)
        assert result.returncode == 0

        # .mcp.json should remain with other server
        assert mcp_json.exists()
        config = json.loads(mcp_json.read_text())
        assert "other" in config["mcpServers"]
        assert "hol" not in config["mcpServers"]

    def test_idempotent(self, project_dir):
        # Uninstall without install should succeed
        result = run_uninstall(project_dir)
        assert result.returncode == 0
