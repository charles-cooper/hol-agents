#!/bin/bash
# hol-agent-helper.sh - HOL4 agent interface for interactive proof development
#
# Usage:
#   ./hol-agent-helper.sh start [DIR]  - Start HOL session in background (optionally in DIR)
#   ./hol-agent-helper.sh send CMD     - Send command and wait for response
#   ./hol-agent-helper.sh send:FILE    - Send contents of FILE
#   ./hol-agent-helper.sh stop         - Stop HOL session
#   ./hol-agent-helper.sh status       - Check if HOL is running
#
# If DIR contains a .hol_init.sml file, it will be loaded after HOL starts.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FIFO_IN=/tmp/hol_agent_in
LOG=/tmp/hol_agent.log
PIDFILE=/tmp/hol_agent.pid
WORKDIR_FILE=/tmp/hol_agent_workdir

# Wait for HOL response (null-terminated output)
# Usage: wait_for_response PREV_SIZE [TIMEOUT_DECISECONDS]
# Returns: 0 on success (output printed), 1 on timeout
wait_for_response() {
    local prev_size="$1"
    local timeout="${2:-3000}"  # default 5 minutes (3000 * 0.1s)
    local elapsed=0

    while [ $elapsed -lt $timeout ]; do
        local curr_size=$(stat -c%s $LOG 2>/dev/null || echo 0)
        if [ "$curr_size" -gt "$prev_size" ]; then
            # Check if last byte is null (response complete)
            if [ "$(tail -c 1 $LOG | od -An -tx1 | tr -d ' ')" = "00" ]; then
                # Extract the last null-terminated segment (NF filters empty segments)
                awk 'BEGIN{RS="\0"} NF {last=$0} END{print last}' $LOG | head -100
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

    if [ -f "$PIDFILE" ] && kill -0 "$(head -1 $PIDFILE)" 2>/dev/null; then
        echo "HOL already running (PID: $(head -1 $PIDFILE))"
        return 0
    fi

    rm -f $FIFO_IN
    mkfifo $FIFO_IN

    # Save working directory for later commands
    echo "$workdir" > $WORKDIR_FILE

    # Start HOL with --zero flag for null-byte framing
    # - tail -f keeps the FIFO open (otherwise first write closes HOL's stdin)
    # - setsid creates new session so HOL isn't killed when parent exits
    # - fd redirections detach from parent's tty so script doesn't wait for HOL
    cd "$workdir"
    setsid sh -c "tail -f $FIFO_IN | hol --zero > $LOG 2>&1" </dev/null >/dev/null 2>&1 &
    PIPELINE_PID=$!

    echo "$PIPELINE_PID" > $PIDFILE

    # Wait for HOL to initialize (look for null byte in log)
    echo "Waiting for HOL to initialize..."
    local timeout=60
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if [ "$(tail -c 1 $LOG 2>/dev/null | od -An -tx1 | tr -d ' ')" = "00" ]; then
            echo "HOL ready (PID: $PIPELINE_PID) in $workdir"

            # Load init file if present
            if [ -f "$workdir/.hol_init.sml" ]; then
                echo "Loading $workdir/.hol_init.sml..."
                send_file "$workdir/.hol_init.sml"
            fi

            return 0
        fi
        sleep 0.1
        elapsed=$((elapsed + 1))
    done

    echo "HOL failed to start (timeout)"
    kill $PIPELINE_PID 2>/dev/null
    rm -f $PIDFILE $WORKDIR_FILE
    return 1
}

send_cmd() {
    local cmd="$1"

    if [ ! -f "$PIDFILE" ]; then
        echo "ERROR: HOL not running. Use: $0 start"
        return 1
    fi

    local prev_size=$(stat -c%s $LOG 2>/dev/null || echo 0)
    printf '%s\0' "$cmd" > $FIFO_IN
    wait_for_response "$prev_size"
}

# Send command via temp file (avoids shell escaping issues)
send_file() {
    local file="$1"

    if [ ! -f "$PIDFILE" ]; then
        echo "ERROR: HOL not running. Use: $0 start"
        return 1
    fi

    if [ ! -f "$file" ]; then
        echo "ERROR: File not found: $file"
        return 1
    fi

    local prev_size=$(stat -c%s $LOG 2>/dev/null || echo 0)
    { cat "$file"; printf '\0'; } > $FIFO_IN
    wait_for_response "$prev_size"
}

stop_hol() {
    if [ ! -f "$PIDFILE" ]; then
        echo "HOL not running"
        return 0
    fi

    local pid=$(head -1 $PIDFILE)

    # setsid creates a new session with session ID = pid
    # Kill entire session to clean up tail -f and hol
    pkill -s $pid 2>/dev/null

    # Fallback: kill the process group
    kill -- -$pid 2>/dev/null

    rm -f $PIDFILE $FIFO_IN $WORKDIR_FILE
    echo "HOL stopped"
}

status_hol() {
    if [ -f "$PIDFILE" ] && kill -0 "$(head -1 $PIDFILE)" 2>/dev/null; then
        local workdir=$(cat $WORKDIR_FILE 2>/dev/null || echo "unknown")
        echo "HOL running (PID: $(head -1 $PIDFILE)) in $workdir"
        return 0
    else
        echo "HOL not running"
        rm -f $PIDFILE 2>/dev/null
        return 1
    fi
}

log_hol() {
    if [ ! -f "$LOG" ]; then
        echo "No log file found"
        return 1
    fi
    tr '\0' '\n' < "$LOG"
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
    log)
        log_hol
        ;;
    *)
        echo "Usage: $0 {start [DIR]|start:DIR|send CMD|send:FILE|stop|status|log}"
        exit 1
        ;;
esac
