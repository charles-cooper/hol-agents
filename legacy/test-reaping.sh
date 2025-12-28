#!/bin/bash
# Test script for process reaping functionality

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HELPER="$SCRIPT_DIR/hol-agent-helper.sh"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

pass() { echo -e "${GREEN}PASS${NC}: $1"; }
fail() { echo -e "${RED}FAIL${NC}: $1"; exit 1; }
info() { echo -e "${YELLOW}TEST${NC}: $1"; }

# Clean up before and after tests
cleanup() {
    "$HELPER" nuke --force >/dev/null 2>&1 || true
}
trap cleanup EXIT

# Run from the main hol-agents directory
cd "$SCRIPT_DIR/.."

cleanup

echo "========================================"
echo "Testing process reaping functionality"
echo "========================================"
echo ""

# Test 1: Session creates activity and created timestamps
info "Session creates activity/created timestamps"
"$HELPER" start >/dev/null 2>&1
SESS_DIR=$(ls -d /tmp/hol_sessions/*/ 2>/dev/null | head -1)
if [ -f "$SESS_DIR/activity" ] && [ -f "$SESS_DIR/created" ]; then
    pass "Timestamps created"
else
    fail "Timestamps not created"
fi

# Test 2: Send updates activity timestamp
info "Send command updates activity timestamp"
OLD_ACTIVITY=$(cat "$SESS_DIR/activity")
sleep 2
"$HELPER" send "1+1;" >/dev/null
NEW_ACTIVITY=$(cat "$SESS_DIR/activity")
if [ "$NEW_ACTIVITY" -gt "$OLD_ACTIVITY" ]; then
    pass "Activity timestamp updated on send"
else
    fail "Activity timestamp not updated (old=$OLD_ACTIVITY, new=$NEW_ACTIVITY)"
fi

# Test 3: Reap keeps active sessions with default timeout
info "Reap keeps active sessions (default timeout)"
"$HELPER" send "2+2;" >/dev/null
OUTPUT=$("$HELPER" reap 2>&1)
if echo "$OUTPUT" | grep -q "Kept:"; then
    pass "Active session kept"
else
    fail "Active session should be kept: $OUTPUT"
fi

# Test 4: Reap kills stale sessions with short timeout
info "Reap kills stale sessions (short timeout)"
sleep 2
OUTPUT=$(REAP_INACTIVE_TIMEOUT=1 "$HELPER" reap 2>&1)
if echo "$OUTPUT" | grep -q "Killed:"; then
    pass "Stale session killed with REAP_INACTIVE_TIMEOUT=1"
else
    fail "Stale session should be killed: $OUTPUT"
fi

# Test 5: Session no longer exists after reap
info "Session directory cleaned up after reap"
if [ ! -d "$SESS_DIR" ]; then
    pass "Session directory removed"
else
    fail "Session directory still exists"
fi

# Test 6: Start new session, test max age timeout
info "Reap kills old sessions (max age timeout)"
"$HELPER" start >/dev/null 2>&1
"$HELPER" send "3+3;" >/dev/null  # Keep it active
sleep 2
OUTPUT=$(REAP_MAX_AGE=1 "$HELPER" reap 2>&1)
if echo "$OUTPUT" | grep -q "Killed:"; then
    pass "Old session killed with REAP_MAX_AGE=1"
else
    fail "Old session should be killed: $OUTPUT"
fi

# Test 7: Nuke shows preview and kills
info "Nuke shows preview with details"
"$HELPER" start >/dev/null 2>&1 || fail "Failed to start session"
OUTPUT=$(timeout 10 "$HELPER" nuke <<< "n" 2>&1) || true
if echo "$OUTPUT" | grep -q "This will kill:" && echo "$OUTPUT" | grep -q "HOL session PID"; then
    pass "Nuke shows detailed preview"
else
    fail "Nuke should show detailed preview: $OUTPUT"
fi

# Test 8: Nuke --force kills and shows details
info "Nuke --force shows details"
OUTPUT=$("$HELPER" nuke --force 2>&1)
if echo "$OUTPUT" | grep -q "Nuking:" && echo "$OUTPUT" | grep -q "HOL session PID"; then
    pass "Nuke --force shows details"
else
    fail "Nuke --force should show details: $OUTPUT"
fi

# Test 9: Nothing to reap when clean
info "Reap reports nothing when clean"
OUTPUT=$("$HELPER" reap 2>&1)
if echo "$OUTPUT" | grep -q "Nothing to reap"; then
    pass "Correctly reports nothing to reap"
else
    fail "Should report nothing to reap: $OUTPUT"
fi

# Test 10: Nothing to nuke when clean
info "Nuke reports nothing when clean"
OUTPUT=$("$HELPER" nuke --force 2>&1)
if echo "$OUTPUT" | grep -q "Nothing to kill"; then
    pass "Correctly reports nothing to kill"
else
    fail "Should report nothing to kill: $OUTPUT"
fi

# Test 11: Session with custom session ID shows in output
info "Session ID shown in reap output"
"$HELPER" -s test-session start >/dev/null 2>&1
OUTPUT=$("$HELPER" reap 2>&1)
if echo "$OUTPUT" | grep -q ":test-session"; then
    pass "Session ID shown in output"
else
    fail "Session ID should be shown: $OUTPUT"
fi
"$HELPER" -s test-session stop >/dev/null 2>&1

# Test 12: Auto-reap at script entry (silent, doesn't affect explicit reap)
info "Auto-reap skipped for explicit reap command"
"$HELPER" start >/dev/null 2>&1
sleep 2
# With short timeout, if auto-reap ran first, explicit reap would show "Nothing to reap"
# But we skip auto-reap for explicit reap, so it should show "Killed:"
OUTPUT=$(REAP_INACTIVE_TIMEOUT=1 "$HELPER" reap 2>&1)
if echo "$OUTPUT" | grep -q "Killed:"; then
    pass "Explicit reap shows kills (auto-reap skipped)"
else
    fail "Explicit reap should show kills: $OUTPUT"
fi

echo ""
echo "========================================"
echo -e "${GREEN}All tests passed!${NC}"
echo "========================================"
