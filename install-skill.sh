#!/bin/bash
# Install the HOL4 skill for Claude Code (project-local)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKILL_DIR="$SCRIPT_DIR/skills/hol4"
PROJECT_CLAUDE_DIR=".claude"
TARGET_DIR="$PROJECT_CLAUDE_DIR/skills"

if [ ! -d "$SKILL_DIR" ]; then
    echo "Error: Skill directory not found: $SKILL_DIR"
    exit 1
fi

if [ ! -d "$PROJECT_CLAUDE_DIR" ]; then
    echo "Error: No .claude directory in current project"
    echo "Run this from a project root with Claude Code initialized"
    exit 1
fi

mkdir -p "$TARGET_DIR"

if [ -L "$TARGET_DIR/hol4" ]; then
    echo "Updating existing symlink..."
    rm "$TARGET_DIR/hol4"
elif [ -e "$TARGET_DIR/hol4" ]; then
    echo "Error: $TARGET_DIR/hol4 exists and is not a symlink"
    echo "Remove it manually if you want to install"
    exit 1
fi

ln -s "$SKILL_DIR" "$TARGET_DIR/hol4"
echo "Installed HOL4 skill: $TARGET_DIR/hol4 -> $SKILL_DIR"
