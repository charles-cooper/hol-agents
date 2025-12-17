# HOL Agent Helper - Contributor Guide

Tool for AI agents to interactively develop HOL4 proofs. See SKILL.md for usage.

## Architecture

### Session Isolation

Each working directory gets isolated session in `/tmp/hol_sessions/<hash>/`:
- `in` - Named FIFO for commands
- `log` - Output (null-byte delimited)
- `pid` - Pipeline PID
- `workdir` - Original directory path
- `session_id` - Session ID (if `HOL_SESSION_ID` was set)

Hash is first 16 chars of SHA256 of `path` or `path:session_id` if `HOL_SESSION_ID` is set.

### Multiple Sessions (Same Directory)

Set `HOL_SESSION_ID` env var to run concurrent sessions in the same directory:
```bash
HOL_SESSION_ID=agent1 ./hol-agent-helper.sh start
HOL_SESSION_ID=agent2 ./hol-agent-helper.sh start
```
Each session ID hashes with the directory to create independent session dirs. All commands must use the same `HOL_SESSION_ID` to target the correct session.

### Null-Byte Framing

HOL started with `--zero` flag. Each response terminated by `\0`.
- `wait_for_response()` polls log for null byte
- `awk 'BEGIN{RS="\0"}'` extracts last segment
- Default timeout: 5 minutes (3000 deciseconds)

### Process Model

```
setsid sh -c "tail -f FIFO | hol --zero > log 2>&1"
```

- `tail -f` keeps FIFO open across multiple writes
- `setsid` detaches from parent (survives script exit)
- Commands: `printf '%s\0' "$cmd" > FIFO`

## Key Functions

| Function | Purpose |
|----------|---------|
| `start_hol` | Create session, start pipeline, load `.hol_init.sml` if exists |
| `send_cmd` | Write command to FIFO, wait for response |
| `send_file` | Send file contents (avoids shell escaping) |
| `load_to` | Dispatch to `load_to_blank` or `load_to_cheat` based on line content |
| `load_to_blank` | Load script prefix up to blank line |
| `load_to_cheat` | Parse proof, replay tactics to cheat point |
| `parse_and_send_tactics` | Handle THEN1/`>-` nesting by splitting at incomplete blocks |
| `interrupt_hol` | SIGINT to HOL process (stop runaway tactics) |

## Design Decisions

**Why FIFO + tail -f?**
Direct pipe closes after first write. tail -f keeps stdin open for persistent session.

**Why null-byte framing?**
HOL output can contain anything. Null bytes are safe delimiters, and `--zero` is built-in.

**Why file-based sends?**
Shell escaping of HOL backquotes (`` ` ``) is fragile. Files bypass escaping entirely.

**Why hash-based session dirs?**
Allows multiple independent sessions. Path in dirname would have slash issues.

## Gotchas

- `pkill -s PID` kills session group - needed because pipeline has multiple processes
- `holdeptool.exe` must exist at `$HOLDIR/bin/` for `load-to` dependency discovery
- Cheat navigation uses awk to track paren depth for THEN1 splitting - complex but necessary
- Session vars (`SESSION_DIR`, etc.) are global - `load_to` updates them when changing directories

## Testing Changes

```bash
# Start session, verify basics
./hol-agent-helper.sh start
./hol-agent-helper.sh send 'val x = 1 + 1;'
./hol-agent-helper.sh status

# Test load-to on a real script
./hol-agent-helper.sh load-to /path/to/script.sml LINE

# Test cheat navigation
./hol-agent-helper.sh load-to /path/to/script.sml CHEAT_LINE

# Cleanup
./hol-agent-helper.sh stop
./hol-agent-helper.sh cleanup  # if needed
```

## Files

```
hol-agent-helper.sh  -- Main script
README.md            -- Human documentation
SKILL.md             -- Consumer agent documentation
AGENTS.md            -- This file (contributor guide)
```
