#!/bin/bash
# Uninstall HOL4 tools from Claude Code (project-local)
set -e

# --- Skills ---
SKILLS_TARGET=".claude/skills/hol4"

if [[ -L "$SKILLS_TARGET" ]]; then
    rm "$SKILLS_TARGET"
    echo "Removed skills symlink: $SKILLS_TARGET"
    # Remove skills directory only if now empty (rmdir fails on non-empty)
    if rmdir ".claude/skills" 2>/dev/null; then
        echo "Removed empty .claude/skills directory"
    fi
elif [[ -e "$SKILLS_TARGET" ]]; then
    echo "WARNING: $SKILLS_TARGET exists but is not a symlink, skipping"
else
    echo "No skills symlink found"
fi

# --- MCP ---
MCP_JSON=".mcp.json"

if [[ ! -f "$MCP_JSON" ]]; then
    echo "No $MCP_JSON found"
    exit 0
fi

if ! command -v jq &>/dev/null; then
    echo "ERROR: jq required to modify $MCP_JSON" >&2
    echo "Install with: sudo apt install jq" >&2
    exit 1
fi

if ! jq -e '.mcpServers.hol' "$MCP_JSON" &>/dev/null; then
    echo "No hol server in $MCP_JSON"
    exit 0
fi

jq 'del(.mcpServers.hol)' "$MCP_JSON" > "$MCP_JSON.tmp" && mv "$MCP_JSON.tmp" "$MCP_JSON"

if jq -e '.mcpServers == {}' "$MCP_JSON" &>/dev/null; then
    rm "$MCP_JSON"
    echo "Removed $MCP_JSON (no servers left)"
else
    echo "Removed hol server from $MCP_JSON"
fi
