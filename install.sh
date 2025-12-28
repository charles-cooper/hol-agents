#!/bin/bash
# Install HOL4 tools for Claude Code (project-local)
# - Skills: /plan, /sketch, /prove commands
# - MCP: hol_start, hol_send, holmake, etc.
set -e

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKILL_DIR="$REPO_DIR/skills/hol4"
MCP_SERVER="$REPO_DIR/hol_mcp_server.py"

# Validate repo
if [[ ! -d "$SKILL_DIR" ]]; then
    echo "ERROR: Skill directory not found: $SKILL_DIR" >&2
    exit 1
fi
if [[ ! -f "$MCP_SERVER" ]]; then
    echo "ERROR: MCP server not found: $MCP_SERVER" >&2
    exit 1
fi

# --- Skills ---
PROJECT_CLAUDE_DIR=".claude"
SKILLS_TARGET="$PROJECT_CLAUDE_DIR/skills"

if [[ ! -d "$PROJECT_CLAUDE_DIR" ]]; then
    echo "ERROR: No .claude directory in current project" >&2
    echo "Run this from a project root with Claude Code initialized" >&2
    exit 1
fi

mkdir -p "$SKILLS_TARGET"

if [[ -L "$SKILLS_TARGET/hol4" ]]; then
    rm "$SKILLS_TARGET/hol4"
elif [[ -e "$SKILLS_TARGET/hol4" ]]; then
    echo "ERROR: $SKILLS_TARGET/hol4 exists and is not a symlink" >&2
    echo "Remove it manually to install" >&2
    exit 1
fi

ln -s "$SKILL_DIR" "$SKILLS_TARGET/hol4"
echo "Installed skills: $SKILLS_TARGET/hol4 -> $SKILL_DIR"

# --- MCP ---
MCP_JSON=".mcp.json"

if [[ -f "$MCP_JSON" ]]; then
    if ! command -v jq &>/dev/null; then
        echo "ERROR: jq required to update existing $MCP_JSON" >&2
        echo "Install with: sudo apt install jq" >&2
        exit 1
    fi
    jq --arg server "$MCP_SERVER" '.mcpServers.hol = {
        "command": "python3",
        "args": [$server]
    }' "$MCP_JSON" > "$MCP_JSON.tmp" && mv "$MCP_JSON.tmp" "$MCP_JSON"
    echo "Updated $MCP_JSON with hol server"
else
    cat > "$MCP_JSON" << EOF
{
  "mcpServers": {
    "hol": {
      "command": "python3",
      "args": ["$MCP_SERVER"]
    }
  }
}
EOF
    echo "Created $MCP_JSON with hol server"
fi

echo ""
echo "HOL4 tools installed. Available in Claude Code:"
echo "  Skills: /plan, /sketch, /prove"
echo "  MCP: hol_start, hol_send, holmake, hol_cursor_*"
