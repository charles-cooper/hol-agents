#!/bin/bash
# hol-agent-helper.sh - HOL4 agent interface for interactive proof development
#
# Usage:
#   ./hol-agent-helper.sh start    - Start HOL session in background
#   ./hol-agent-helper.sh send CMD - Send command and wait for response
#   ./hol-agent-helper.sh stop     - Stop HOL session
#   ./hol-agent-helper.sh status   - Check if HOL is running

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FIFO_IN=/tmp/hol_agent_in
LOG=/tmp/hol_agent.log
PIDFILE=/tmp/hol_agent.pid
CMDFILE="$SCRIPT_DIR/.hol_cmd.sml"

start_hol() {
    if [ -f "$PIDFILE" ] && kill -0 "$(head -1 $PIDFILE)" 2>/dev/null; then
        echo "HOL already running (PID: $(head -1 $PIDFILE))"
        return 0
    fi

    rm -f $FIFO_IN $LOG
    mkfifo $FIFO_IN
    touch $LOG

    # Start HOL reading from FIFO, output to log
    # tail -f keeps the FIFO open (otherwise first write closes HOL's stdin)
    tail -f $FIFO_IN | stdbuf -oL hol 2>&1 | tee -a $LOG &
    PIPELINE_PID=$!

    echo "$PIPELINE_PID" > $PIDFILE

    # Wait for HOL to initialize (look for the prompt in log)
    echo "Waiting for HOL to initialize..."
    local timeout=50
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if grep -q "For introductory HOL help" $LOG 2>/dev/null; then
            sleep 1  # Give it a moment more
            echo "HOL ready (PID: $PIPELINE_PID)"
            return 0
        fi
        sleep 0.1
        elapsed=$((elapsed + 1))
    done

    echo "HOL failed to start (timeout)"
    kill $PIPELINE_PID 2>/dev/null
    rm -f $PIDFILE
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
    rm -f $PIDFILE $FIFO_IN
    echo "HOL stopped"
}

status_hol() {
    if [ -f "$PIDFILE" ] && kill -0 "$(awk '{print $1}' $PIDFILE)" 2>/dev/null; then
        echo "HOL running (PID: $(awk '{print $1}' $PIDFILE))"
        return 0
    else
        echo "HOL not running"
        rm -f $PIDFILE 2>/dev/null
        return 1
    fi
}

case "$1" in
    start)
        start_hol
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
        echo "Usage: $0 {start|send CMD|send:FILE|stop|status}"
        exit 1
        ;;
esac
