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

start_hol() {
    local workdir="${1:-.}"
    workdir="$(cd "$workdir" && pwd)"

    if [ -f "$PIDFILE" ] && kill -0 "$(head -1 $PIDFILE)" 2>/dev/null; then
        echo "HOL already running (PID: $(head -1 $PIDFILE))"
        return 0
    fi

    rm -f $FIFO_IN $LOG
    mkfifo $FIFO_IN
    touch $LOG

    # Save working directory for later commands
    echo "$workdir" > $WORKDIR_FILE

    # Start HOL reading from FIFO, output to log
    # Use script -qfc to force PTY allocation for proper unbuffering
    cd "$workdir"
    tail -f $FIFO_IN | script -qfc "hol" /dev/null 2>&1 | tee -a $LOG &
    PIPELINE_PID=$!

    echo "$PIPELINE_PID" > $PIDFILE

    # Wait for HOL to initialize (look for the prompt in log)
    echo "Waiting for HOL to initialize..."
    local timeout=60
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if grep -q "For introductory HOL help" $LOG 2>/dev/null; then
            sleep 0.5  # Give it a moment more
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
    local sentinel="AGENT_DONE_$(date +%s%N)"

    if [ ! -f "$PIDFILE" ]; then
        echo "ERROR: HOL not running. Use: $0 start"
        return 1
    fi

    # Get the log size before sending command
    local prev_size=$(stat -c%s $LOG 2>/dev/null || echo 0)

    # Send command through FIFO
    echo "$cmd" > $FIFO_IN
    echo "val _ = print \"$sentinel\\n\";" > $FIFO_IN

    # Wait for sentinel in output
    local timeout=3000  # 5 minutes (3000 * 0.1s)
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if tail -c +$((prev_size + 1)) $LOG 2>/dev/null | grep -qa "$sentinel"; then
            # Print new output, excluding sentinel and prompts
            tail -c +$((prev_size + 1)) $LOG | sed "/$sentinel/d" | grep -av "^> " | head -100
            return 0
        fi
        sleep 0.1
        elapsed=$((elapsed + 1))
    done
    echo "TIMEOUT waiting for response"
    return 1
}

# Send command via temp file (avoids shell escaping issues)
# Usage: ./hol-agent-helper.sh send:FILE where FILE contains SML code
send_file() {
    local file="$1"
    local sentinel="AGENT_DONE_$(date +%s%N)"

    if [ ! -f "$PIDFILE" ]; then
        echo "ERROR: HOL not running. Use: $0 start"
        return 1
    fi

    if [ ! -f "$file" ]; then
        echo "ERROR: File not found: $file"
        return 1
    fi

    # Get the log size before sending command
    local prev_size=$(stat -c%s $LOG 2>/dev/null || echo 0)

    # Send file contents through FIFO
    cat "$file" > $FIFO_IN
    echo "" > $FIFO_IN  # Ensure newline
    echo "val _ = print \"$sentinel\\n\";" > $FIFO_IN

    # Wait for sentinel in output
    local timeout=3000  # 5 minutes (3000 * 0.1s)
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if tail -c +$((prev_size + 1)) $LOG 2>/dev/null | grep -qa "$sentinel"; then
            # Print new output, excluding sentinel and prompts
            tail -c +$((prev_size + 1)) $LOG | sed "/$sentinel/d" | grep -av "^> " | head -100
            return 0
        fi
        sleep 0.1
        elapsed=$((elapsed + 1))
    done
    echo "TIMEOUT waiting for response"
    return 1
}

stop_hol() {
    if [ ! -f "$PIDFILE" ]; then
        echo "HOL not running"
        return 0
    fi

    read HOL_PID CAT_PID < $PIDFILE
    kill $HOL_PID $CAT_PID 2>/dev/null
    # Also kill any script/tail processes
    pkill -P $HOL_PID 2>/dev/null
    rm -f $PIDFILE $FIFO_IN $WORKDIR_FILE
    echo "HOL stopped"
}

status_hol() {
    if [ -f "$PIDFILE" ] && kill -0 "$(awk '{print $1}' $PIDFILE)" 2>/dev/null; then
        local workdir=$(cat $WORKDIR_FILE 2>/dev/null || echo "unknown")
        echo "HOL running (PID: $(awk '{print $1}' $PIDFILE)) in $workdir"
        return 0
    else
        echo "HOL not running"
        rm -f $PIDFILE 2>/dev/null
        return 1
    fi
}

case "$1" in
    start)
        shift
        start_hol "$1"
        ;;
    start:*)
        # start:DIR - start in DIR
        start_hol "${1#start:}"
        ;;
    send)
        shift
        send_cmd "$*"
        ;;
    send:*)
        # send:FILE - send contents of FILE
        send_file "${1#send:}"
        ;;
    stop)
        stop_hol
        ;;
    status)
        status_hol
        ;;
    *)
        echo "Usage: $0 {start [DIR]|start:DIR|send CMD|send:FILE|stop|status}"
        exit 1
        ;;
esac
