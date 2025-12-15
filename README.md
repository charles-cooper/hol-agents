# HOL4 Agent Helper

A simple shell script for AI agents to interactively develop proofs in HOL4, similar to how humans use emacs hol-mode or vim-hol.

## Overview

This tool provides a persistent HOL4 session that agents can interact with via simple shell commands. It enables the "send tactic, see goal, send next tactic" workflow essential for interactive theorem proving.

## Requirements

- HOL4 installed and `hol` available in PATH
- Bash shell
- Standard Unix tools (`tail`, `grep`, `sed`, `stat`)

## Installation

```bash
chmod +x hol-agent-helper.sh
```

## Usage

### Start a HOL session

```bash
./hol-agent-helper.sh start
```

### Send commands

For simple commands without special characters:
```bash
./hol-agent-helper.sh send 'val x = 1 + 1;'
```

For commands with backquotes (term quotations), use a file:
```bash
echo 'g `!m:num. m + 0 = m`;' > .hol_cmd.sml
./hol-agent-helper.sh send:.hol_cmd.sml
```

### Check status

```bash
./hol-agent-helper.sh status           # Check current directory
./hol-agent-helper.sh status:/path/to/dir  # Check specific directory
```

### Stop the session

```bash
./hol-agent-helper.sh stop
```

### Load a script up to a specific point (recommended for proof development)

```bash
./hol-agent-helper.sh load-to SCRIPT_FILE LINE_NUMBER
```

This command loads a HOL script file up to a specified line, automatically handling all dependencies. This is the **recommended way** to set up a session for interactive proof development on an existing script.

**Requirements:**
- `LINE_NUMBER` must point to a blank line in the script
- The blank line should follow a "block ender" (`End`, `QED`, `Termination`, or a line ending with `;`)
- The script should be buildable (compiles with Holmake, possibly with cheats)
- Requires `holdeptool.exe` at `~/HOL/bin/holdeptool.exe`

**What it does:**
1. Validates the line is blank and follows a block ender
2. Uses `holdeptool.exe` to discover all dependencies
3. Restarts HOL session in the script's directory
4. Loads all dependencies automatically
5. Executes the script content up to (but not including) the target line

**Example:**
```bash
# Find a good stopping point (blank line after QED)
grep -n "^QED$" myScript.sml
sed -n '240,250p' myScript.sml  # Check lines around QED

# Load up to line 245 (a blank line after QED on line 244)
./hol-agent-helper.sh load-to /path/to/myScript.sml 245

# Now interact with the session - all prior definitions are available
./hol-agent-helper.sh send 'my_previous_def;'
```

## Example Proof Session

```bash
# Start HOL
./hol-agent-helper.sh start

# Load arithmetic theory
./hol-agent-helper.sh send 'open arithmeticTheory;'

# Set a goal (using file to avoid shell escaping)
echo 'g `!m:num. m + 0 = m`;' > .hol_cmd.sml
./hol-agent-helper.sh send:.hol_cmd.sml
# Output: Initial goal: ∀m. m + 0 = m

# Apply induction
echo 'e (Induct_on `m`);' > .hol_cmd.sml
./hol-agent-helper.sh send:.hol_cmd.sml
# Output: 2 subgoals: base case and step case

# Solve with simplification
echo 'e (asm_simp_tac bool_ss [ADD_CLAUSES]);' > .hol_cmd.sml
./hol-agent-helper.sh send:.hol_cmd.sml
# Output: Goal proved. ⊢ ∀m. m + 0 = m

# Extract the theorem
echo 'val my_thm = top_thm();' > .hol_cmd.sml
./hol-agent-helper.sh send:.hol_cmd.sml
```

## How It Works

The script uses a named pipe (FIFO) to send commands to a persistent HOL process:

1. `tail -f` keeps the FIFO open so multiple commands can be sent
2. Commands are echoed to the FIFO
3. A sentinel value is printed after each command to detect completion
4. Output is captured from a log file

## Useful HOL Commands

```sml
(* Goal management *)
g `...`;           (* set goal *)
e (tactic);        (* expand with tactic *)
p();               (* print current goal *)
b();               (* backup one step *)
drop();            (* drop current goal *)
top_thm();         (* get proved theorem *)

(* Search *)
DB.match [] ``pattern``;     (* find theorems matching pattern *)
DB.find "name";              (* find theorems by name *)

(* Proof state *)
proofManagerLib.status();    (* show proof status *)
```

## Files

Session files are stored per-directory in `/tmp/hol_sessions/<hash>/`:
- `in` - Named pipe for sending commands
- `log` - Output log
- `pid` - PID file for the session
- `workdir` - Working directory path

The `<hash>` is derived from the working directory path, allowing multiple independent sessions.

## Agent Instructions

See [AGENTS.md](AGENTS.md) for detailed instructions on how AI agents should use this tool.

## License

MIT
