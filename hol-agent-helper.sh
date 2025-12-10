#!/bin/bash
# hol-agent-helper.sh - HOL4 agent interface for interactive proof development
#
# Usage:
#   ./hol-agent-helper.sh start [DIR]  - Start HOL session (default: current directory)
#   ./hol-agent-helper.sh send CMD     - Send command and wait for response
#   ./hol-agent-helper.sh send:FILE    - Send contents of FILE
#   ./hol-agent-helper.sh stop         - Stop HOL session for current directory
#   ./hol-agent-helper.sh status       - Check if HOL is running for current directory
#   ./hol-agent-helper.sh log          - Show session log
#   ./hol-agent-helper.sh cleanup      - Kill ALL HOL sessions (nuclear option)
#
# Session isolation:
#   Each working directory gets its own isolated HOL session. Sessions are stored
#   in /tmp/hol_sessions/<hash>/ where <hash> is derived from the absolute path.
#   This means:
#   - Multiple projects can have independent HOL sessions
#   - Sessions are automatically cleaned up on system reboot
#   - All commands (send, stop, status, log) must be run from the same directory
#     where 'start' was run (or a directory specified to 'start')
#   - Running from subdirectories will NOT find the parent's session
#
# If DIR contains a .hol_init.sml file, it will be loaded after HOL starts.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SESSIONS_DIR="/tmp/hol_sessions"

# Compute session directory from working directory path
# Uses first 16 chars of sha256 hash for brevity while avoiding collisions
session_dir_for() {
    local workdir="$1"
    local hash=$(echo -n "$workdir" | sha256sum | cut -c1-16)
    echo "$SESSIONS_DIR/$hash"
}

# Get paths for current session
SESSION_DIR=$(session_dir_for "$(pwd)")
FIFO_IN="$SESSION_DIR/in"
LOG="$SESSION_DIR/log"
PIDFILE="$SESSION_DIR/pid"
WORKDIR_FILE="$SESSION_DIR/workdir"

# Wait for HOL response (null-terminated output)
# Usage: wait_for_response PREV_SIZE [TIMEOUT_DECISECONDS]
# Returns: 0 on success (output printed), 1 on timeout
wait_for_response() {
    local prev_size="$1"
    local timeout="${2:-3000}"  # default 5 minutes (3000 * 0.1s)
    local elapsed=0

    while [ $elapsed -lt $timeout ]; do
        local curr_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)
        if [ "$curr_size" -gt "$prev_size" ]; then
            # Check if last byte is null (response complete)
            if [ "$(tail -c 1 "$LOG" | od -An -tx1 | tr -d ' ')" = "00" ]; then
                # Extract the last null-terminated segment (NF filters empty segments)
                awk 'BEGIN{RS="\0"} NF {last=$0} END{print last}' "$LOG" | head -100
                return 0
            fi
        fi
        sleep 0.1
        elapsed=$((elapsed + 1))
    done
    echo "TIMEOUT waiting for response"
    return 1
}

start_hol() {
    local workdir="${1:-.}"
    workdir="$(cd "$workdir" && pwd)"

    # Compute session dir for the target workdir (not cwd)
    local sess_dir=$(session_dir_for "$workdir")
    local fifo="$sess_dir/in"
    local log="$sess_dir/log"
    local pidfile="$sess_dir/pid"
    local workdir_file="$sess_dir/workdir"

    if [ -f "$pidfile" ] && kill -0 "$(head -1 "$pidfile")" 2>/dev/null; then
        echo "HOL already running (PID: $(head -1 "$pidfile")) in $workdir"
        return 0
    fi

    # Create session directory
    mkdir -p "$sess_dir"
    rm -f "$fifo"
    mkfifo "$fifo"

    # Save working directory for status command
    echo "$workdir" > "$workdir_file"

    # Start HOL with --zero flag for null-byte framing
    # - tail -f keeps the FIFO open (otherwise first write closes HOL's stdin)
    # - setsid creates new session so HOL isn't killed when parent exits
    # - fd redirections detach from parent's tty so script doesn't wait for HOL
    cd "$workdir"
    setsid sh -c "tail -f '$fifo' | hol --zero > '$log' 2>&1" </dev/null >/dev/null 2>&1 &
    local pipeline_pid=$!

    echo "$pipeline_pid" > "$pidfile"

    # Wait for HOL to initialize (look for null byte in log)
    echo "Waiting for HOL to initialize..."
    local timeout=60
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if [ "$(tail -c 1 "$log" 2>/dev/null | od -An -tx1 | tr -d ' ')" = "00" ]; then
            echo "HOL ready (PID: $pipeline_pid) in $workdir"

            # Load init file if present
            if [ -f "$workdir/.hol_init.sml" ]; then
                echo "Loading $workdir/.hol_init.sml..."
                # Temporarily update globals for send_file
                SESSION_DIR="$sess_dir"
                FIFO_IN="$fifo"
                LOG="$log"
                PIDFILE="$pidfile"
                send_file "$workdir/.hol_init.sml"
            fi

            return 0
        fi
        sleep 0.1
        elapsed=$((elapsed + 1))
    done

    echo "HOL failed to start (timeout)"
    kill "$pipeline_pid" 2>/dev/null
    rm -rf "$sess_dir"
    return 1
}

send_cmd() {
    local cmd="$1"

    if [ ! -f "$PIDFILE" ]; then
        echo "ERROR: HOL not running in $(pwd). Use: $0 start"
        return 1
    fi

    local prev_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)
    printf '%s\0' "$cmd" > "$FIFO_IN"
    wait_for_response "$prev_size"
}

# Send command via temp file (avoids shell escaping issues)
send_file() {
    local file="$1"

    if [ ! -f "$PIDFILE" ]; then
        echo "ERROR: HOL not running in $(pwd). Use: $0 start"
        return 1
    fi

    if [ ! -f "$file" ]; then
        echo "ERROR: File not found: $file"
        return 1
    fi

    local prev_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)
    { cat "$file"; printf '\0'; } > "$FIFO_IN"
    wait_for_response "$prev_size"
}

stop_hol() {
    if [ ! -f "$PIDFILE" ]; then
        echo "HOL not running in $(pwd)"
        return 0
    fi

    local pid=$(head -1 "$PIDFILE")

    # setsid creates a new session with session ID = pid
    # Kill entire session to clean up tail -f and hol
    pkill -s "$pid" 2>/dev/null

    # Fallback: kill the process group
    kill -- -"$pid" 2>/dev/null

    rm -rf "$SESSION_DIR"
    echo "HOL stopped"
}

status_hol() {
    if [ -f "$PIDFILE" ] && kill -0 "$(head -1 "$PIDFILE")" 2>/dev/null; then
        local workdir=$(cat "$WORKDIR_FILE" 2>/dev/null || echo "unknown")
        echo "HOL running (PID: $(head -1 "$PIDFILE")) in $workdir"
        return 0
    else
        echo "HOL not running in $(pwd)"
        # Clean up stale session if exists
        [ -d "$SESSION_DIR" ] && rm -rf "$SESSION_DIR"
        return 1
    fi
}

log_hol() {
    if [ ! -f "$LOG" ]; then
        echo "No log file found for $(pwd)"
        return 1
    fi
    tr '\0' '\n' < "$LOG"
}

# Kill all HOL sessions - nuclear option for cleanup
cleanup_all() {
    local count=0

    # Kill all hol --zero processes
    if pkill -f "hol --zero" 2>/dev/null; then
        echo "Killed hol processes"
        count=$((count + 1))
    fi

    # Kill any orphaned tail -f processes for our FIFOs
    if pkill -f "tail -f /tmp/hol_sessions/.*/in" 2>/dev/null; then
        echo "Killed tail processes"
        count=$((count + 1))
    fi

    # Remove all session directories
    if [ -d "$SESSIONS_DIR" ]; then
        local sessions=$(ls -1 "$SESSIONS_DIR" 2>/dev/null | wc -l)
        rm -rf "$SESSIONS_DIR"
        echo "Removed $sessions session(s)"
    fi

    if [ $count -eq 0 ]; then
        echo "No HOL sessions found"
    else
        echo "Cleanup complete"
    fi
}

case "$1" in
    start)
        shift
        start_hol "$1"
        ;;
    start:*)
        start_hol "${1#start:}"
        ;;
    send)
        shift
        send_cmd "$*"
        ;;
    send:*)
        send_file "${1#send:}"
        ;;
    stop)
        stop_hol
        ;;
    status)
        status_hol
        ;;
    status:*)
        # Allow checking status of a specific directory
        cd "${1#status:}" && status_hol
        ;;
    log)
        log_hol
        ;;
    cleanup)
        cleanup_all
        ;;
    *)
        echo "Usage: $0 {start [DIR]|send CMD|send:FILE|stop|status|log|cleanup}"
        echo ""
        echo "Commands operate on the HOL session for the current directory."
        echo "Use 'cleanup' to kill ALL sessions (nuclear option)."
        exit 1
        ;;
esac
