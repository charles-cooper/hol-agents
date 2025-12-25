#!/bin/bash
# Test script for hol-agent-helper.sh interrupt functionality
#
# Tests:
# 1. Interrupt command stops long-running tactic, session stays usable
# 2. Signal forwarding: SIGTERM to send process forwards interrupt to HOL

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HELPER="$SCRIPT_DIR/hol-agent-helper.sh"

# Create temp directory for test
TEST_DIR=$(mktemp -d)
cleanup() {
    cd "$TEST_DIR" && "$HELPER" stop 2>/dev/null || true
    rm -rf "$TEST_DIR"
}
trap cleanup EXIT

cd "$TEST_DIR"

PASS=0
FAIL=0

pass() {
    echo "PASS: $1"
    PASS=$((PASS + 1))
}

fail() {
    echo "FAIL: $1"
    FAIL=$((FAIL + 1))
}

echo "=== Testing hol-agent-helper.sh interrupt functionality ==="
echo "Test directory: $TEST_DIR"
echo ""

# Start HOL session
echo "Starting HOL session..."
"$HELPER" start >/dev/null 2>&1

# Verify it started
if ! "$HELPER" status | grep -q "HOL running"; then
    fail "Could not start HOL session"
    exit 1
fi
echo "HOL session started."
echo ""

# Test 1: Interrupt command stops long-running operation
echo "--- Test 1: Interrupt command stops long-running operation ---"

# Send a command that loops until interrupted
# In SML, this creates an infinite loop that SIGINT should break
echo "Sending long-running command in background..."

# Run send in background - this will hang until interrupted
"$HELPER" send 'let fun loop n = loop (n+1) in loop 0 end;' &
SEND_PID=$!

# Give it time to start executing
sleep 2

# Verify send is still running (the loop hasn't finished)
if ! kill -0 "$SEND_PID" 2>/dev/null; then
    fail "Send process exited unexpectedly (loop may have finished)"
else
    echo "Loop is running, sending interrupt..."

    # Send interrupt
    "$HELPER" interrupt >/dev/null 2>&1

    # Wait a bit for send to exit
    sleep 2

    # Check if send exited (it should after interrupt)
    if kill -0 "$SEND_PID" 2>/dev/null; then
        # Force kill if still running
        kill "$SEND_PID" 2>/dev/null
        wait "$SEND_PID" 2>/dev/null || true
        fail "Interrupt did not stop the operation (send still running)"
    else
        wait "$SEND_PID" 2>/dev/null || true
        echo "Interrupt stopped the operation."

        # Verify session is still usable
        sleep 1
        RESPONSE=$("$HELPER" send '1 + 1;' 2>&1)
        if echo "$RESPONSE" | grep -q "val it = 2"; then
            pass "Interrupt works: stopped loop, session still usable"
        else
            fail "Session not usable after interrupt. Response: $RESPONSE"
        fi
    fi
fi

echo ""

# Test 2: Signal forwarding - SIGTERM to send forwards interrupt to HOL
echo "--- Test 2: Signal forwarding (SIGTERM to send) ---"

# Send another long-running command in background
echo "Sending long-running command in background..."
"$HELPER" send 'let fun loop n = loop (n+1) in loop 0 end;' &
SEND_PID=$!

# Give it time to start
sleep 2

# Verify it's running
if ! kill -0 "$SEND_PID" 2>/dev/null; then
    fail "Send process exited unexpectedly"
else
    echo "Loop is running, sending SIGTERM to send process (PID: $SEND_PID)..."

    # Send SIGTERM to the send process - should trigger forward_interrupt trap
    kill -TERM "$SEND_PID" 2>/dev/null

    # Wait for it to exit
    sleep 2

    # Check if send exited
    if kill -0 "$SEND_PID" 2>/dev/null; then
        kill -9 "$SEND_PID" 2>/dev/null
        wait "$SEND_PID" 2>/dev/null || true
        fail "Send process did not exit after SIGTERM"
    else
        wait "$SEND_PID" 2>/dev/null || true
        echo "Send process exited after SIGTERM."

        # Verify session is still usable (interrupt was forwarded)
        sleep 1
        RESPONSE=$("$HELPER" send '2 + 2;' 2>&1)
        if echo "$RESPONSE" | grep -q "val it = 4"; then
            pass "Signal forwarding works: SIGTERM forwarded interrupt, session still usable"
        else
            # Could be that interrupt wasn't forwarded - session might be stuck
            # Try one more time with explicit interrupt
            "$HELPER" interrupt >/dev/null 2>&1
            sleep 1
            RESPONSE=$("$HELPER" send '2 + 2;' 2>&1)
            if echo "$RESPONSE" | grep -q "val it = 4"; then
                fail "Signal forwarding partially works: needed explicit interrupt to recover"
            else
                fail "Session not usable after SIGTERM. Response: $RESPONSE"
            fi
        fi
    fi
fi

echo ""

# Stop the session
"$HELPER" stop >/dev/null 2>&1

echo "=== Test Results ==="
echo "Passed: $PASS"
echo "Failed: $FAIL"

if [ "$FAIL" -gt 0 ]; then
    exit 1
else
    exit 0
fi
