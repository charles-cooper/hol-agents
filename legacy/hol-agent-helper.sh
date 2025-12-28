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
#   ./hol-agent-helper.sh reap         - Kill stale sessions and old build processes
#   ./hol-agent-helper.sh nuke         - Kill ALL HOL-related processes (nuclear option)
#
# Session isolation:
#   Each working directory gets its own isolated HOL session. Sessions are stored
#   in /tmp/hol_sessions/<hash>/ where <hash> is derived from the absolute path
#   and optional session ID.
#   This means:
#   - Multiple projects can have independent HOL sessions
#   - Multiple sessions in the same directory are supported via HOL_SESSION_ID
#   - Sessions are automatically cleaned up on system reboot
#   - All commands (send, stop, status, log) must be run from the same directory
#     where 'start' was run (or a directory specified to 'start')
#   - Running from subdirectories will NOT find the parent's session
#
# Multiple sessions in same directory:
#   Use -s flag or HOL_SESSION_ID environment variable:
#     ./hol-agent-helper.sh -s agent1 start
#     HOL_SESSION_ID=agent2 ./hol-agent-helper.sh start
#   Each session ID creates an independent session in the same directory.
#
# If DIR contains a .hol_init.sml file, it will be loaded after HOL starts.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SESSIONS_DIR="/tmp/hol_sessions"

# Reaping timeouts (can be overridden via environment variables)
REAP_INACTIVE_TIMEOUT=${REAP_INACTIVE_TIMEOUT:-7200}   # 2h in seconds
REAP_MAX_AGE=${REAP_MAX_AGE:-28800}                    # 8h in seconds
REAP_BUILD_TIMEOUT=${REAP_BUILD_TIMEOUT:-7200}        # 2h in seconds

# Parse -s flag for session ID (must come before command)
if [ "$1" = "-s" ]; then
    HOL_SESSION_ID="$2"
    shift 2
fi

# Compute session directory from working directory path and optional session ID
# Uses first 16 chars of sha256 hash for brevity while avoiding collisions
# If HOL_SESSION_ID is set, it's included in the hash to allow multiple sessions
session_dir_for() {
    local workdir="$1"
    local session_key="$workdir"
    if [ -n "$HOL_SESSION_ID" ]; then
        session_key="$workdir:$HOL_SESSION_ID"
    fi
    local hash=$(echo -n "$session_key" | sha256sum | cut -c1-16)
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

# Get PID of HOL REPL process (buildheap) for current session
# Prints PID to stdout, returns 1 if not found
get_hol_pid() {
    local session_leader=$(head -1 "$PIDFILE" 2>/dev/null)
    [ -z "$session_leader" ] && return 1
    pgrep -s "$session_leader" -f "buildheap" 2>/dev/null | head -1
}

# Forward SIGINT to HOL process (silent version for traps)
forward_interrupt() {
    local hol_pid=$(get_hol_pid)
    [ -n "$hol_pid" ] && kill -INT "$hol_pid" 2>/dev/null
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
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "HOL already running (PID: $(head -1 "$pidfile")) in $workdir$session_msg"
        return 0
    fi

    # Create session directory
    mkdir -p "$sess_dir"
    rm -f "$fifo"
    mkfifo "$fifo"

    # Save working directory and session ID for status command
    echo "$workdir" > "$workdir_file"
    echo "$HOL_SESSION_ID" > "$sess_dir/session_id"

    # Start HOL with --zero flag for null-byte framing
    # - We use cat to read from FIFO, with a background sleep keeping the FIFO open
    #   (tail -f doesn't work reliably with FIFOs - it uses inotify which doesn't trigger)
    # - setsid creates new session so HOL isn't killed when parent exits
    # - fd redirections detach from parent's tty so script doesn't wait for HOL
    cd "$workdir"
    local hol_bin="${HOLDIR:-$HOME/HOL}/bin/hol"
    # sleep infinity keeps write end of FIFO open so cat doesn't see EOF after first command
    # cat reads from FIFO reliably (unlike tail -f which has inotify issues with FIFOs)
    # We write the session leader PID to a file so interrupt can find the hol process
    setsid sh -c "echo \$\$ > '$sess_dir/leader_pid'; sleep infinity > '$fifo' & cat '$fifo' | '$hol_bin' --zero > '$log' 2>&1" </dev/null >/dev/null 2>&1 &

    # Wait for leader_pid file to be written
    local wait_count=0
    while [ ! -s "$sess_dir/leader_pid" ] && [ $wait_count -lt 20 ]; do
        sleep 0.05
        wait_count=$((wait_count + 1))
    done
    if [ ! -s "$sess_dir/leader_pid" ]; then
        echo "Failed to get session leader PID"
        rm -rf "$sess_dir"
        return 1
    fi
    local pipeline_pid=$(cat "$sess_dir/leader_pid")

    echo "$pipeline_pid" > "$pidfile"
    date +%s > "$sess_dir/created"
    date +%s > "$sess_dir/activity"

    # Wait for HOL to initialize (look for null byte in log)
    echo "Waiting for HOL to initialize..."
    local timeout=60
    local elapsed=0
    while [ $elapsed -lt $timeout ]; do
        if [ "$(tail -c 1 "$log" 2>/dev/null | od -An -tx1 | tr -d ' ')" = "00" ]; then
            local session_msg=""
            [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
            echo "HOL ready (PID: $pipeline_pid) in $workdir$session_msg"

            # Temporarily update globals for send_file
            SESSION_DIR="$sess_dir"
            FIFO_IN="$fifo"
            LOG="$log"
            PIDFILE="$pidfile"

            # Load etq (goaltree helper)
            local etq_file="$SCRIPT_DIR/sml_helpers/etq.sml"
            if [ -f "$etq_file" ]; then
                echo "Loading etq.sml..."
                send_file "$etq_file"
            fi

            # Load project init file if present
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
    kill "$pipeline_pid" 2>/dev/null
    rm -rf "$sess_dir"
    return 1
}

send_cmd() {
    local cmd="$1"

    if [ ! -f "$PIDFILE" ]; then
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "ERROR: HOL not running in $(pwd)$session_msg. Use: $0 start"
        return 1
    fi

    trap 'forward_interrupt; exit 130' INT TERM HUP QUIT
    local prev_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)
    date +%s > "$SESSION_DIR/activity"
    printf '%s\0' "$cmd" > "$FIFO_IN"
    wait_for_response "$prev_size"
    trap - INT TERM HUP QUIT
}

# Send command via temp file (avoids shell escaping issues)
send_file() {
    local file="$1"

    if [ ! -f "$PIDFILE" ]; then
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "ERROR: HOL not running in $(pwd)$session_msg. Use: $0 start"
        return 1
    fi

    if [ ! -f "$file" ]; then
        echo "ERROR: File not found: $file"
        return 1
    fi

    trap 'forward_interrupt; exit 130' INT TERM HUP QUIT
    local prev_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)
    date +%s > "$SESSION_DIR/activity"
    { cat "$file"; printf '\0'; } > "$FIFO_IN"
    wait_for_response "$prev_size"
    trap - INT TERM HUP QUIT
}

stop_hol() {
    if [ ! -f "$PIDFILE" ]; then
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "HOL not running in $(pwd)$session_msg"
        return 0
    fi

    local pid=$(head -1 "$PIDFILE")
    local saved_session_id=$(cat "$SESSION_DIR/session_id" 2>/dev/null)

    # setsid creates a new session with session ID = pid
    # Kill entire session to clean up tail -f and hol
    pkill -s "$pid" 2>/dev/null

    # Fallback: kill the process group
    kill -- -"$pid" 2>/dev/null

    rm -rf "$SESSION_DIR"
    local session_msg=""
    [ -n "$saved_session_id" ] && session_msg=" [session: $saved_session_id]"
    echo "HOL stopped$session_msg"
}

status_hol() {
    if [ -f "$PIDFILE" ] && kill -0 "$(head -1 "$PIDFILE")" 2>/dev/null; then
        local workdir=$(cat "$WORKDIR_FILE" 2>/dev/null || echo "unknown")
        local saved_session_id=$(cat "$SESSION_DIR/session_id" 2>/dev/null)
        local session_msg=""
        [ -n "$saved_session_id" ] && session_msg=" [session: $saved_session_id]"
        echo "HOL running (PID: $(head -1 "$PIDFILE")) in $workdir$session_msg"
        return 0
    else
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "HOL not running in $(pwd)$session_msg"
        # Clean up stale session if exists
        [ -d "$SESSION_DIR" ] && rm -rf "$SESSION_DIR"
        return 1
    fi
}

log_hol() {
    if [ ! -f "$LOG" ]; then
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "No log file found for $(pwd)$session_msg"
        return 1
    fi
    tr '\0' '\n' < "$LOG"
}

# Load script up to a given line number
# Usage: load_to SCRIPT_FILE LINE_NUMBER
#
# If LINE_NUMBER points to a blank line: loads up to start of next top-level block
# If LINE_NUMBER points to a line containing 'cheat': navigates into the proof to that cheat
load_to() {
    local script_file="$1"
    local line_num="$2"

    if [ -z "$script_file" ] || [ -z "$line_num" ]; then
        echo "Usage: $0 load-to SCRIPT_FILE LINE_NUMBER"
        return 1
    fi

    if [ ! -f "$script_file" ]; then
        echo "ERROR: Script file not found: $script_file"
        return 1
    fi

    # Get absolute path
    script_file="$(cd "$(dirname "$script_file")" && pwd)/$(basename "$script_file")"
    local script_dir="$(dirname "$script_file")"

    # Validate line number is a positive integer
    if ! [[ "$line_num" =~ ^[0-9]+$ ]] || [ "$line_num" -lt 1 ]; then
        echo "ERROR: Line number must be a positive integer"
        return 1
    fi

    # Check total lines in file
    local total_lines=$(wc -l < "$script_file")
    if [ "$line_num" -gt "$total_lines" ]; then
        echo "ERROR: Line $line_num exceeds file length ($total_lines lines)"
        return 1
    fi

    # Check what's on the target line
    local target_line=$(sed -n "${line_num}p" "$script_file")

    # Determine mode: blank line or cheat line
    if [ -z "$(echo "$target_line" | tr -d '[:space:]')" ]; then
        # Blank line mode - existing behavior
        load_to_blank "$script_file" "$line_num" "$script_dir"
    elif echo "$target_line" | grep -q "cheat"; then
        # Cheat mode - new behavior
        load_to_cheat "$script_file" "$line_num" "$script_dir"
    else
        echo "ERROR: Line $line_num is neither blank nor contains 'cheat':"
        echo "  '$target_line'"
        echo "The load-to command requires either a blank line or a cheat line."
        return 1
    fi
}

# Load to a blank line (original behavior)
load_to_blank() {
    local script_file="$1"
    local line_num="$2"
    local script_dir="$3"

    # Find closest non-blank line above and validate it looks like a block ender
    local prev_line_num=$((line_num - 1))
    local prev_line=""
    while [ "$prev_line_num" -ge 1 ]; do
        prev_line=$(sed -n "${prev_line_num}p" "$script_file")
        if [ -n "$(echo "$prev_line" | tr -d '[:space:]')" ]; then
            break
        fi
        prev_line_num=$((prev_line_num - 1))
    done

    if [ "$prev_line_num" -ge 1 ]; then
        # Check if it's a block ender: single capitalized word (End, QED, Termination) OR ends with semicolon
        local trimmed=$(echo "$prev_line" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        if [[ "$trimmed" =~ ^[A-Z][A-Za-z]*$ ]] || [[ "$trimmed" =~ \;$ ]]; then
            echo "Block ender found at line $prev_line_num: $trimmed"
        else
            echo "WARNING: Line $prev_line_num doesn't look like a block ender: '$trimmed'"
            echo "Expected single capitalized word (End, QED, etc.) or line ending with semicolon."
            echo "Proceeding anyway..."
        fi
    fi

    # Common setup: dependencies, session start, script prefix execution
    load_to_common_setup "$script_file" "$line_num" "$script_dir"
}

# Load to a cheat line (new behavior)
load_to_cheat() {
    local script_file="$1"
    local cheat_line="$2"
    local script_dir="$3"

    echo "Cheat detected at line $cheat_line. Navigating into proof..."

    # Find the Theorem/Triviality block containing this cheat
    local theorem_line=""
    local theorem_name=""
    local i=$cheat_line
    while [ "$i" -ge 1 ]; do
        local line=$(sed -n "${i}p" "$script_file")
        if echo "$line" | grep -qE "^(Theorem|Triviality)[[:space:]]"; then
            theorem_line=$i
            # Extract theorem name (word after Theorem/Triviality, before colon or [)
            theorem_name=$(echo "$line" | sed -E 's/^(Theorem|Triviality)[[:space:]]+([A-Za-z0-9_]+).*/\2/')
            break
        fi
        i=$((i - 1))
    done

    if [ -z "$theorem_line" ]; then
        echo "ERROR: Could not find Theorem/Triviality containing line $cheat_line"
        return 1
    fi
    echo "Found theorem '$theorem_name' at line $theorem_line"

    # Find the Proof line
    local proof_line=""
    i=$theorem_line
    while [ "$i" -le "$cheat_line" ]; do
        local line=$(sed -n "${i}p" "$script_file")
        if echo "$line" | grep -qE "^Proof"; then
            proof_line=$i
            break
        fi
        i=$((i + 1))
    done

    if [ -z "$proof_line" ]; then
        echo "ERROR: Could not find 'Proof' between theorem (line $theorem_line) and cheat (line $cheat_line)"
        return 1
    fi
    echo "Found Proof at line $proof_line"

    # Find a blank line before the theorem to use as load point
    local load_line=$((theorem_line - 1))
    while [ "$load_line" -ge 1 ]; do
        local line=$(sed -n "${load_line}p" "$script_file")
        if [ -z "$(echo "$line" | tr -d '[:space:]')" ]; then
            break
        fi
        load_line=$((load_line - 1))
    done

    if [ "$load_line" -lt 1 ]; then
        echo "ERROR: Could not find blank line before theorem"
        return 1
    fi

    # Load up to before the theorem
    echo "Loading script up to line $load_line (before theorem)..."
    load_to_common_setup "$script_file" "$load_line" "$script_dir"
    if [ $? -ne 0 ]; then
        return 1
    fi

    # Extract goal text (between theorem declaration and Proof)
    echo "Extracting goal..."
    local goal_text=$(sed -n "$((theorem_line + 1)),$((proof_line - 1))p" "$script_file" | tr '\n' ' ')
    # Also get any text after the colon on the theorem line itself
    local theorem_line_text=$(sed -n "${theorem_line}p" "$script_file")
    local after_colon=$(echo "$theorem_line_text" | sed 's/^[^:]*://')
    if [ -n "$(echo "$after_colon" | tr -d '[:space:]')" ]; then
        goal_text="$after_colon $goal_text"
    fi

    # Clean up goal text
    goal_text=$(echo "$goal_text" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')

    # Send goal
    echo "Setting up goal..."
    local tmpfile=$(mktemp --suffix=.sml)
    echo "g \`$goal_text\`;" > "$tmpfile"
    local result=$(send_file "$tmpfile")
    rm -f "$tmpfile"
    if ! echo "$result" | grep -q "Initial goal:"; then
        echo "ERROR setting goal - no goal established: $result"
        return 1
    fi

    # Extract and parse tactics from Proof+1 to cheat_line-1
    echo "Parsing tactics..."
    parse_and_send_tactics "$script_file" "$((proof_line + 1))" "$((cheat_line - 1))" "$cheat_line"

    echo ""
    echo "Session ready at cheat on line $cheat_line of $script_file"
    echo "Use 'send' to interact with the session."
}

# Parse tactics and send them, handling THEN1 nesting
# Arguments: script_file start_line end_line cheat_line
parse_and_send_tactics() {
    local script_file="$1"
    local start_line="$2"
    local end_line="$3"
    local cheat_line="$4"

    # Read all tactic lines into a single string
    local all_tactics=$(sed -n "${start_line},${end_line}p" "$script_file")

    # Strategy: Find incomplete THEN1 blocks by tracking paren depth.
    # A THEN1 opener is >- ( or THEN1 ( (with optional whitespace).
    # A block is "complete" if its ( is matched by ) before end of text.
    # A block is "incomplete" if we reach end of text with unmatched (.
    # We only split at incomplete blocks.

    # Use awk to find split points (character positions of incomplete >- ( or THEN1 ()
    local split_info=$(echo "$all_tactics" | awk '
    BEGIN {
        depth = 0
        in_then1 = 0
        then1_start = -1
        pos = 0
        split_points = ""
    }
    {
        line = $0
        n = length(line)
        for (i = 1; i <= n; i++) {
            c = substr(line, i, 1)
            pos++

            # Check for >- pattern (look ahead for - after >)
            if (c == ">" && i < n) {
                rest = substr(line, i+1)
                if (match(rest, /^[[:space:]]*-[[:space:]]*\(/)) {
                    # Found >- (, record position before >
                    then1_starts[depth] = pos - 1
                    then1_depths[depth] = depth
                    # Skip past the pattern to the (
                    skip = RLENGTH
                    i += skip
                    pos += skip
                    depth++
                    continue
                }
            }

            # Check for THEN1 pattern
            if (c == "T" && substr(line, i, 5) == "THEN1") {
                rest = substr(line, i+5)
                if (match(rest, /^[[:space:]]*\(/)) {
                    then1_starts[depth] = pos - 1
                    then1_depths[depth] = depth
                    skip = 4 + RLENGTH
                    i += skip
                    pos += skip
                    depth++
                    continue
                }
            }

            if (c == "(") {
                depth++
            } else if (c == ")") {
                depth--
                # Check if this closes a THEN1 block
                for (d in then1_depths) {
                    if (then1_depths[d] == depth) {
                        # This THEN1 block is now complete, remove from tracking
                        delete then1_starts[d]
                        delete then1_depths[d]
                    }
                }
            }
        }
        pos++  # newline
    }
    END {
        # Any remaining then1_starts are incomplete - output their positions
        n = 0
        for (d in then1_starts) {
            if (n > 0) printf " "
            printf "%d", then1_starts[d]
            n++
        }
        if (n > 0) printf "\n"
    }
    ')

    if [ -z "$split_info" ]; then
        # No incomplete THEN1 blocks - send everything as one chunk
        echo "No incomplete THEN1 blocks found, sending as single chunk..."
        send_tactic_chunk "$all_tactics"
        return
    fi

    echo "Found incomplete THEN1 blocks at positions: $split_info"

    # Convert split points to sorted array
    local -a splits
    read -ra splits <<< "$split_info"
    IFS=$'\n' splits=($(sort -n <<<"${splits[*]}")); unset IFS

    # Build chunks based on split points
    local prev_pos=0
    local chunk_num=0
    local all_len=${#all_tactics}

    for split_pos in "${splits[@]}"; do
        if [ "$split_pos" -gt "$prev_pos" ]; then
            chunk_num=$((chunk_num + 1))
            local chunk="${all_tactics:$prev_pos:$((split_pos - prev_pos))}"
            echo "  Sending chunk $chunk_num (chars $prev_pos-$split_pos)..."
            send_tactic_chunk "$chunk"
        fi
        # Skip past the >- ( or THEN1 ( to start next chunk after the (
        # Find the ( after this position
        local rest="${all_tactics:$split_pos}"
        # Use grep to find the pattern and calculate offset
        local pattern_match=$(echo "$rest" | grep -oP '^(>\s*-|THEN1)\s*\(' | head -1)
        local paren_offset=${#pattern_match}
        if [ "$paren_offset" -eq 0 ]; then
            # Fallback: just skip a reasonable amount
            paren_offset=4
        fi
        prev_pos=$((split_pos + paren_offset))
    done

    # Send final chunk
    if [ "$prev_pos" -lt "$all_len" ]; then
        chunk_num=$((chunk_num + 1))
        local chunk="${all_tactics:$prev_pos}"
        echo "  Sending final chunk $chunk_num..."
        send_tactic_chunk "$chunk"
    fi
}

# Helper: send a single tactic chunk
send_tactic_chunk() {
    local chunk="$1"

    # Trim leading/trailing whitespace from the whole chunk
    # but preserve internal structure including \\ operators
    chunk=$(printf '%s' "$chunk" | sed -e '1s/^[[:space:]]*//' -e '$s/[[:space:]]*$//')

    # If chunk starts with \\, remove just that leading \\
    # (it would be a continuation from before a split point)
    chunk=$(printf '%s' "$chunk" | sed '1s/^\\\\[[:space:]]*//')

    # If chunk ends with \\, remove just that trailing \\
    # (it would continue to an incomplete >- block we split at)
    chunk=$(printf '%s' "$chunk" | sed '$s/[[:space:]]*\\\\[[:space:]]*$//')

    # Check if anything remains
    if [ -z "$(printf '%s' "$chunk" | tr -d '[:space:]')" ]; then
        return
    fi

    local preview=$(printf '%s' "$chunk" | tr '\n' ' ' | cut -c1-60)
    echo "    Content: $preview..."

    local tmpfile=$(mktemp --suffix=.sml)
    printf 'e (%s);\n' "$chunk" > "$tmpfile"

    local prev_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)
    { cat "$tmpfile"; printf '\0'; } > "$FIFO_IN"
    local result=$(wait_for_response "$prev_size" 1200)  # 2 min timeout per chunk

    rm -f "$tmpfile"

    if echo "$result" | grep -qi "error\|exception"; then
        echo "WARNING: Error in tactic chunk:"
        echo "$result" | head -10
    fi
}

# Common setup for both blank and cheat modes
load_to_common_setup() {
    local script_file="$1"
    local line_num="$2"
    local script_dir="$3"

    # Get dependencies using holdeptool.exe
    echo "Getting dependencies with holdeptool.exe..."
    local holdeptool="${HOLDIR:-$HOME/HOL}/bin/holdeptool.exe"
    if [ ! -x "$holdeptool" ]; then
        echo "ERROR: holdeptool.exe not found at $holdeptool"
        return 1
    fi

    local deps=$("$holdeptool" "$script_file" 2>&1)
    if [ $? -ne 0 ]; then
        echo "ERROR: holdeptool.exe failed: $deps"
        return 1
    fi

    # Stop any existing session and start fresh in the script's directory
    echo "Restarting HOL session in $script_dir..."
    cd "$script_dir"

    # Update session variables for the new directory
    SESSION_DIR=$(session_dir_for "$script_dir")
    FIFO_IN="$SESSION_DIR/in"
    LOG="$SESSION_DIR/log"
    PIDFILE="$SESSION_DIR/pid"
    WORKDIR_FILE="$SESSION_DIR/workdir"

    stop_hol 2>/dev/null
    start_hol "$script_dir"
    if [ $? -ne 0 ]; then
        echo "ERROR: Failed to start HOL"
        return 1
    fi

    # Load dependencies
    echo "Loading dependencies..."
    local dep_count=0
    for dep in $deps; do
        # Skip empty lines
        [ -z "$dep" ] && continue
        echo "  Loading $dep..."
        local result=$(send_cmd "load \"$dep\";")
        if echo "$result" | grep -q "Exception\|Error"; then
            echo "WARNING: Problem loading $dep: $result"
        fi
        dep_count=$((dep_count + 1))
    done
    echo "Loaded $dep_count dependencies."

    # Extract lines 1 to line_num-1 from the script
    if [ "$line_num" -gt 1 ]; then
        # Write directly to temp file (avoids shell variable size limits)
        local tmpfile=$(mktemp)
        head -n $((line_num - 1)) "$script_file" > "$tmpfile"
        local file_size=$(stat -c%s "$tmpfile")
        echo "Executing script up to line $((line_num - 1)) ($file_size bytes)..."

        local prev_size=$(stat -c%s "$LOG" 2>/dev/null || echo 0)

        # Write in background to avoid blocking on FIFO buffer (64KB default)
        # HOL consumes gradually as it executes, so large writes would block
        { cat "$tmpfile"; printf '\0'; } > "$FIFO_IN" &
        local write_pid=$!

        # Use longer timeout for script execution
        echo "Waiting for script execution (this may take a while)..."
        wait_for_response "$prev_size" 6000  # 10 minute timeout
        local result=$?

        # Clean up background write (should be done, but just in case)
        wait $write_pid 2>/dev/null
        rm -f "$tmpfile"

        if [ $result -ne 0 ]; then
            echo "WARNING: Script execution may have timed out"
        fi
    fi

    echo ""
    echo "Session ready at line $line_num of $script_file"
    echo "Use 'send' to interact with the session."
}

# Send interrupt signal to HOL process
# This can stop looping tactics without killing the session
interrupt_hol() {
    if [ ! -f "$PIDFILE" ]; then
        local session_msg=""
        [ -n "$HOL_SESSION_ID" ] && session_msg=" [session: $HOL_SESSION_ID]"
        echo "HOL not running in $(pwd)$session_msg"
        return 1
    fi

    local hol_pid=$(get_hol_pid)

    if [ -n "$hol_pid" ]; then
        echo "Sending SIGINT to HOL process (PID: $hol_pid)..."
        kill -INT "$hol_pid" 2>/dev/null
        sleep 0.5
        echo "Interrupt sent. Check session with 'send' command."
        return 0
    else
        echo "Could not find HOL process to interrupt"
        return 1
    fi
}

# Reap stale HOL sessions
# Args: verbose (true/false)
# Returns: count via global REAP_COUNT
reap_stale_sessions() {
    local verbose="${1:-false}"
    REAP_COUNT=0

    for sess in "$SESSIONS_DIR"/*/; do
        [ -d "$sess" ] || continue
        [ -f "$sess/pid" ] || continue

        local pid=$(cat "$sess/pid")
        local workdir=$(cat "$sess/workdir" 2>/dev/null || echo "unknown")
        local sess_id=$(cat "$sess/session_id" 2>/dev/null)
        local hash=$(basename "$sess" | cut -c1-8)
        local label="$workdir"
        [ -n "$sess_id" ] && label="$label:$sess_id"
        label="$label ($hash)"

        # Already dead? Clean up directory
        if ! kill -0 "$pid" 2>/dev/null; then
            [ "$verbose" = "true" ] && echo "  Cleaned up: $label (dead)"
            rm -rf "$sess"
            continue
        fi

        local now=$(date +%s)
        local activity=$(cat "$sess/activity" 2>/dev/null || stat -c%Y "$sess/pid" 2>/dev/null || echo "$now")
        local created=$(cat "$sess/created" 2>/dev/null || stat -c%Y "$sess/pid" 2>/dev/null || echo "$now")
        local inactive=$((now - activity))
        local age=$((now - created))

        # Kill if: inactive > REAP_INACTIVE_TIMEOUT OR age > REAP_MAX_AGE
        if [ "$inactive" -gt "$REAP_INACTIVE_TIMEOUT" ] || [ "$age" -gt "$REAP_MAX_AGE" ]; then
            [ "$verbose" = "true" ] && echo "  Killed: $label (inactive $((inactive/60))m, age $((age/60))m)"
            pkill -s "$pid" 2>/dev/null
            kill -- -"$pid" 2>/dev/null
            rm -rf "$sess"
            REAP_COUNT=$((REAP_COUNT + 1))
        else
            [ "$verbose" = "true" ] && echo "  Kept: $label (inactive $((inactive/60))m, age $((age/60))m)"
        fi
    done
}

# Reap old build processes (holmake, buildheap older than 2h)
# Args: verbose (true/false)
# Returns: count via global REAP_BUILD_COUNT
reap_old_builds() {
    local verbose="${1:-false}"
    REAP_BUILD_COUNT=0

    while read -r pid etime cmd; do
        [ -z "$pid" ] && continue
        if echo "$cmd" | grep -qE 'Holmake|buildheap' && ! echo "$cmd" | grep -qE 'grep|awk'; then
            local shortcmd=$(echo "$cmd" | cut -c1-40)
            if [ "$etime" -gt "$REAP_BUILD_TIMEOUT" ]; then
                [ "$verbose" = "true" ] && echo "  Killed: PID $pid (age $((etime/60))m) - $shortcmd"
                kill "$pid" 2>/dev/null
                REAP_BUILD_COUNT=$((REAP_BUILD_COUNT + 1))
            else
                [ "$verbose" = "true" ] && echo "  Kept: PID $pid (age $((etime/60))m) - $shortcmd"
            fi
        fi
    done < <(ps -eo pid,etimes,cmd 2>/dev/null | tail -n +2)
}

# Reap command - verbose selective cleanup
reap_cmd() {
    echo "Reaping stale HOL sessions..."
    reap_stale_sessions true

    echo "Reaping old build processes..."
    reap_old_builds true

    local total=$((REAP_COUNT + REAP_BUILD_COUNT))
    if [ "$total" -eq 0 ]; then
        echo "Nothing to reap."
    else
        echo "Reaped $total process(es)."
    fi
}

# Nuke - nuclear option, kill everything HOL-related
nuke_cmd() {
    local force=false
    [ "$1" = "--force" ] || [ "$1" = "-f" ] && force=true

    # Count HOL sessions from our tracking
    local hol_count=0
    local hol_pids=""
    for sess in "$SESSIONS_DIR"/*/; do
        [ -f "$sess/pid" ] || continue
        local pid=$(cat "$sess/pid")
        if kill -0 "$pid" 2>/dev/null; then
            hol_pids="$hol_pids $pid"
            hol_count=$((hol_count + 1))
        fi
    done

    # Count holmake processes (match binary path to avoid grep false positives)
    local holmake_pids=$(pgrep -f 'bin/Holmake' 2>/dev/null || true)
    local holmake_count=0
    [ -n "$holmake_pids" ] && holmake_count=$(echo "$holmake_pids" | wc -l)

    # Count standalone buildheap (not part of our sessions)
    # Our sessions spawn buildheap as a child process
    local buildheap_pids=""
    local buildheap_count=0
    for pid in $(pgrep -f 'bin/buildheap' 2>/dev/null || true); do
        # Check if this buildheap's parent is one of our session PIDs
        local ppid=$(ps -p "$pid" -o ppid= 2>/dev/null | tr -d ' ')
        local is_session_child=false
        for sess_pid in $hol_pids; do
            [ "$ppid" = "$sess_pid" ] && is_session_child=true && break
        done
        if [ "$is_session_child" = "false" ]; then
            buildheap_pids="$buildheap_pids $pid"
            buildheap_count=$((buildheap_count + 1))
        fi
    done

    local total=$((hol_count + holmake_count + buildheap_count))

    if [ "$total" -eq 0 ]; then
        echo "Nothing to kill."
        # Still clean up any stale session directories
        rm -rf "$SESSIONS_DIR"/* 2>/dev/null
        return 0
    fi

    # Build detailed info for preview/kill
    local details=""
    for pid in $hol_pids; do
        local workdir=""
        local sess_id=""
        local hash=""
        for sess in "$SESSIONS_DIR"/*/; do
            if [ -f "$sess/pid" ] && [ "$(cat "$sess/pid")" = "$pid" ]; then
                workdir=$(cat "$sess/workdir" 2>/dev/null)
                sess_id=$(cat "$sess/session_id" 2>/dev/null)
                hash=$(basename "$sess" | cut -c1-8)
                break
            fi
        done
        local label="${workdir:-unknown}"
        [ -n "$sess_id" ] && label="$label:$sess_id"
        [ -n "$hash" ] && label="$label ($hash)"
        details="$details  HOL session PID $pid - $label\n"
    done
    for pid in $holmake_pids; do
        local cmd=$(ps -p "$pid" -o args= 2>/dev/null | cut -c1-60)
        details="$details  holmake PID $pid${cmd:+ - $cmd}\n"
    done
    for pid in $buildheap_pids; do
        local cmd=$(ps -p "$pid" -o args= 2>/dev/null | cut -c1-60)
        details="$details  buildheap PID $pid${cmd:+ - $cmd}\n"
    done

    if [ "$force" != "true" ]; then
        echo "This will kill:"
        printf "$details"
        printf "Continue? [y/N] "
        read -r answer
        if [ "$answer" != "y" ] && [ "$answer" != "Y" ]; then
            echo "Aborted."
            return 1
        fi
        echo "Nuking..."
    else
        echo "Nuking:"
        printf "$details"
    fi

    # Kill HOL sessions (use process group kill)
    for pid in $hol_pids; do
        pkill -s "$pid" 2>/dev/null
        kill -- -"$pid" 2>/dev/null
    done

    # Kill holmake
    for pid in $holmake_pids; do
        kill "$pid" 2>/dev/null
    done

    # Kill buildheap
    for pid in $buildheap_pids; do
        kill "$pid" 2>/dev/null
    done

    # Remove all session directories
    rm -rf "$SESSIONS_DIR"/* 2>/dev/null

    echo "Nuked $total process(es)."
}

# Auto-reap stale sessions at script entry (silent)
# Skip if running explicit reap/nuke command (they handle it themselves)
if [ "$1" != "reap" ] && [ "$1" != "nuke" ]; then
    reap_stale_sessions false >/dev/null
fi

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
    reap)
        reap_cmd
        ;;
    nuke)
        shift
        nuke_cmd "$1"
        ;;
    load-to)
        shift
        load_to "$1" "$2"
        ;;
    interrupt)
        interrupt_hol
        ;;
    *)
        echo "Usage: $0 [-s SESSION_ID] {start [DIR]|send CMD|send:FILE|stop|status|log|reap|nuke|load-to FILE LINE|interrupt}"
        echo ""
        echo "Commands operate on the HOL session for the current directory."
        echo "Use -s or HOL_SESSION_ID env var for multiple sessions in the same directory."
        echo ""
        echo "Cleanup commands:"
        echo "  reap         - Kill stale sessions (inactive >2h) and old builds (>2h)"
        echo "  nuke         - Kill ALL HOL-related processes (prompts for confirmation)"
        echo "  nuke --force - Kill ALL without prompting"
        echo ""
        echo "Reap timeouts (override via environment variables):"
        echo "  REAP_INACTIVE_TIMEOUT  - Session inactive timeout in seconds (default: 7200 = 2h)"
        echo "  REAP_MAX_AGE           - Session max age in seconds (default: 28800 = 8h)"
        echo "  REAP_BUILD_TIMEOUT     - Build process timeout in seconds (default: 7200 = 2h)"
        exit 1
        ;;
esac
