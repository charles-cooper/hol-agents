# HOL4 Agent Helper

A simple shell script for AI agents to interactively develop proofs in HOL4, similar to how humans use emacs hol-mode or vim-hol.

## Overview

This tool provides a persistent HOL4 session that agents can interact with via simple shell commands. It enables the "send tactic, see goal, send next tactic" workflow essential for interactive theorem proving.

## Installing as a Claude Code Skill

To use this with [Claude Code](https://claude.com/claude-code), install the skill so Claude automatically knows how to use the helper script for HOL4 proof development. See the [Claude Code skills documentation](https://docs.anthropic.com/en/docs/claude-code/skills) for more details.

**Option 1: Use the install script**
```bash
# From your HOL4 project directory (must have .claude/ initialized)
/path/to/hol-agents/install-skill.sh
```

**Option 2: Manual symlink**
```bash
# Project-level (shared with team via git)
mkdir -p .claude/skills
ln -s /path/to/hol-agents/skills/hol .claude/skills/hol

# Or personal (available in all projects)
mkdir -p ~/.claude/skills
ln -s /path/to/hol-agents/skills/hol ~/.claude/skills/hol
```

After installation, Claude will automatically use the skill when working with HOL4 proofs, .sml theorem files, or Holmake builds.

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

When using multiple sessions, include the session ID in filenames to avoid conflicts:
```bash
echo 'g `!m:num. m + 0 = m`;' > .hol_cmd_${HOL_SESSION_ID}.sml
./hol-agent-helper.sh -s $HOL_SESSION_ID send:.hol_cmd_${HOL_SESSION_ID}.sml
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

### Interrupt a runaway tactic

```bash
./hol-agent-helper.sh interrupt
```

Sends SIGINT to the HOL process without killing the session. Useful when a tactic loops or takes too long. The session remains usable - check with `send` command afterward.

### Maintenance commands

For cleaning up stale or runaway processes:

```bash
./hol-agent-helper.sh reap          # Kill stale sessions + old builds
./hol-agent-helper.sh nuke          # Kill ALL HOL processes (prompts y/n)
./hol-agent-helper.sh nuke --force  # Kill ALL without prompt
```

**reap** kills:
- HOL sessions inactive >2h or older than 8h total
- Holmake/buildheap processes running >2h

**nuke** kills:
- All tracked HOL sessions
- All Holmake processes
- All standalone buildheap processes

Timeouts are configurable via `REAP_INACTIVE_TIMEOUT`, `REAP_MAX_AGE`, `REAP_BUILD_TIMEOUT` environment variables (in seconds).

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

### Navigating to a Cheat

The `load-to` command can also navigate directly to a `cheat` within a proof:

```bash
# Navigate to a specific cheat (line 1439 contains "cheat")
./hol-agent-helper.sh load-to /path/to/script.sml 1439
```

**Semantics based on target line content:**
- **Blank line**: Load up to start of next top-level block (existing behavior)
- **Line contains `cheat`**: Navigate into the proof to that cheat point
- **Other**: Error

**How cheat navigation works:**

1. Finds the containing Theorem block (searches backwards for `Theorem`/`Triviality`)
2. Loads script up to before the Theorem (using existing logic)
3. Extracts goal text between `Theorem name:` and `Proof`, sends `g(`goal`)`
4. Parses tactics from `Proof` to the cheat, handling THEN1 nesting
5. Sends appropriate `e()` calls to reach the cheat point

**Handling THEN1/`>-` nesting:**

The challenge is that `>-` expects its argument to fully solve a subgoal. To stop *inside* a `>-` block, the execution must be split.

A "THEN1 opener" is detected when a line ends with `>- (` (the opening paren of a subgoal block).

- **Complete THEN1 block**: The matching `)` appears before the cheat line. Include in current `e()` call since it fully solves its subgoal.
- **Incomplete THEN1 block**: The matching `)` is at or after the cheat line. Split here:
  - Execute tactics up to (but not including) the `>- (` as one `e()` call
  - Start a new chunk with the inner content (excluding the `>- (`)

**Example:** For a proof with structure:
```sml
Proof
  tac1 \\ tac2 \\ conj_tac      (* creates 2 subgoals *)
  >- (                           (* incomplete: closes after cheat *)
    IF_CASES_TAC                 (* creates 2 subgoals *)
    >- (                         (* incomplete: closes after cheat *)
      inner1 \\ inner2
      \\ cheat)                  (* LINE 1439 *)
    \\ other_case)
  \\ second_conjunct
QED
```

The navigation produces:
```
Chunk 1: tac1 \\ tac2 \\ conj_tac     →  e(tac1 \\ tac2 \\ conj_tac)
Chunk 2: IF_CASES_TAC                  →  e(IF_CASES_TAC)
Chunk 3: inner1 \\ inner2              →  e(inner1 \\ inner2)
```

After execution, the proof state is at the point just before `cheat`.

**Current limitations:**
- Only handles THEN1/`>-` nesting structure
- Does not handle `by` or `suffices_by` nesting (errors if detected)
- Requires the script to be buildable

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
- `session_id` - Session ID (if `HOL_SESSION_ID` was set)

The `<hash>` is derived from the working directory path (and optional session ID), allowing multiple independent sessions.

## Multiple Sessions in Same Directory

To run multiple concurrent HOL sessions in the same directory, use the `-s` flag or `HOL_SESSION_ID` environment variable:

```bash
# Start two independent sessions
./hol-agent-helper.sh -s agent1 start
./hol-agent-helper.sh -s agent2 start

# Interact with specific sessions
./hol-agent-helper.sh -s agent1 send 'val x = 1;'
./hol-agent-helper.sh -s agent2 send 'val y = 2;'

# Check status of each
./hol-agent-helper.sh -s agent1 status
./hol-agent-helper.sh -s agent2 status

# Stop specific session
./hol-agent-helper.sh -s agent1 stop

# Environment variable also works
HOL_SESSION_ID=agent1 ./hol-agent-helper.sh status
```

The session ID is hashed together with the directory path to create unique session directories. All commands (send, stop, status, log, etc.) must use the same session ID to target the correct session.

## Agent Instructions

See [AGENTS.md](AGENTS.md) for detailed instructions on how AI agents should use this tool.

## License

MIT
