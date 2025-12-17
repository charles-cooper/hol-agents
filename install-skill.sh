#!/bin/bash
# Install the HOL4 skill for Claude Code (project-local)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKILL_DIR="$SCRIPT_DIR/skills/hol"
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

if [ -L "$TARGET_DIR/hol" ]; then
    echo "Updating existing symlink..."
    rm "$TARGET_DIR/hol"
elif [ -e "$TARGET_DIR/hol" ]; then
    echo "Error: $TARGET_DIR/hol exists and is not a symlink"
    echo "Remove it manually if you want to install"
    exit 1
fi

ln -s "$SKILL_DIR" "$TARGET_DIR/hol"
echo "Installed HOL skill: $TARGET_DIR/hol -> $SKILL_DIR"
