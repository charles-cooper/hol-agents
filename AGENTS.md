# HOL4 Agent Helper - Instructions for AI Agents

This document describes how AI agents should use the `hol-agent-helper.sh` script to interactively develop proofs in HOL4.

## Quick Reference

| Command | Description |
|---------|-------------|
| `./hol-agent-helper.sh start` | Start HOL session |
| `./hol-agent-helper.sh send 'code'` | Send simple SML code |
| `./hol-agent-helper.sh send:FILE` | Send contents of FILE |
| `./hol-agent-helper.sh stop` | Stop HOL session |
| `./hol-agent-helper.sh status` | Check if HOL is running for current dir |
| `./hol-agent-helper.sh load-to FILE LINE` | **Load script up to LINE (recommended)** |
| `./hol-agent-helper.sh cleanup` | Kill ALL HOL sessions |

## Recommended Workflow: Using `load-to`

When working on an existing HOL script file, **use `load-to` to set up your session**. This is much more reliable than manually loading dependencies and replaying tactics.

### Step 1: Find the right line number

The line number must be a **blank line** that follows a block ender (`End`, `QED`, or line ending with `;`).

```bash
# Find QED lines to identify theorem boundaries
grep -n "^QED$" /path/to/script.sml

# Look at lines around a specific location
sed -n '1240,1250p' /path/to/script.sml
```

### Step 2: Load the script

```bash
~/hol-agents/hol-agent-helper.sh load-to /path/to/script.sml 1245
```

This automatically:
- Discovers all dependencies using `holdeptool.exe`
- Restarts HOL in the script's directory
- Loads all dependencies
- Executes the script up to (but not including) line 1245

### Step 3: Verify and explore

```bash
# Check that definitions are available
~/hol-agents/hol-agent-helper.sh send 'some_def;'

# Now explore tactics interactively
~/hol-agents/hol-agent-helper.sh send 'g `...`;'
~/hol-agents/hol-agent-helper.sh send 'e(tactic);'
```

### Step 4: If session hangs or needs reset

```bash
# Just run load-to again - it handles stopping and restarting
~/hol-agents/hol-agent-helper.sh load-to /path/to/script.sml 1245
```

## Alternative: Manual Setup

If you need to start a fresh session without loading a script, use the basic commands:

```bash
./hol-agent-helper.sh start
```

This starts a persistent HOL session. You then need to manually load dependencies.

## Sending Commands

### Simple Commands

For SML code without backquotes, use `send` directly:

```bash
./hol-agent-helper.sh send 'val x = 1 + 1;'
./hol-agent-helper.sh send 'open arithmeticTheory;'
```

### Commands with Term Quotations

HOL4 uses backquotes for term quotations (e.g., `` `!x. P x` ``). Shell escaping makes this difficult. **Always use a temp file for commands containing backquotes:**

```bash
# Write the command to a file
# (Use your file writing tool to create .hol_cmd.sml)

# Then send it
./hol-agent-helper.sh send:.hol_cmd.sml
```

The temp file should be named `.hol_cmd.sml` in the script directory.

## Proof Workflow

### 1. Set a Goal

Write goal to file and send:
```sml
(* .hol_cmd.sml *)
g `!n. n + 0 = n`;
```

Expected output:
```
Proof manager status: 1 proof.
1. Incomplete goalstack:
     Initial goal:
     ∀n. n + 0 = n
```

### 2. Apply Tactics

Write tactic to file and send:
```sml
(* .hol_cmd.sml *)
e (Induct_on `n`);
```

Expected output shows subgoals:
```
OK..
2 subgoals:
    0.  n + 0 = n
   ------------------------------------
        SUC n + 0 = SUC n

   0 + 0 = 0
```

### 3. Continue Until Proof Complete

Keep applying tactics until you see:
```
Goal proved.
[...] ⊢ statement
Initial goal proved.
⊢ full_theorem: proof
```

### 4. Extract the Theorem

```sml
(* .hol_cmd.sml *)
val my_theorem = top_thm();
```

## Common Tactics

| Tactic | Usage | Description |
|--------|-------|-------------|
| `Induct_on` | ``e (Induct_on `n`);`` | Induction on variable |
| `Cases_on` | ``e (Cases_on `x`);`` | Case split |
| `rw` | `e (rw [thm1, thm2]);` | Rewrite with theorems |
| `simp` | `e (simp []);` | Simplification |
| `asm_simp_tac` | `e (asm_simp_tac bool_ss [thms]);` | Simp with assumptions |
| `metis_tac` | `e (metis_tac [thms]);` | First-order reasoning |
| `DISCH_TAC` | `e DISCH_TAC;` | Move antecedent to assumptions |
| `first_assum` | `e (first_assum ACCEPT_TAC);` | Use first matching assumption |
| `ALL_TAC` | `e ALL_TAC;` | Do nothing (useful in THEN chains) |

## Goal Management Commands

| Command | Description |
|---------|-------------|
| `p();` | Print current goal |
| `b();` | Backup one step |
| `drop();` | Drop current proof |
| `top_thm();` | Get proved theorem |
| `r 1;` | Rotate subgoals |
| `proofManagerLib.status();` | Show all proof status |

## Searching for Theorems

```sml
(* Find theorems by name *)
DB.find "ADD";

(* Find theorems matching a pattern *)
DB.match [] ``_ + 0``;

(* Find theorems in a specific theory *)
DB.theorems "arithmetic";
```

## Loading Theories

Common theories to load:
```sml
open arithmeticTheory;    (* Natural number arithmetic *)
open listTheory;          (* Lists *)
open stringTheory;        (* Strings *)
open optionTheory;        (* Option type *)
open pairTheory;          (* Pairs *)
open wordsTheory;         (* Machine words *)
```

## Error Handling

### Parse Errors

If you see "Record field x not registered", you likely have a parsing issue. Check:
1. Are you using the right quotation marks? HOL uses backticks `` ` ``, not regular quotes
2. Did you load the required theory?

### Tactic Failures

If a tactic fails, you'll see an exception. Use `p();` to see the current goal and try a different approach.

### Timeout

Commands have a 5-minute timeout. For long-running tactics, this should be sufficient. If you hit timeout, check if HOL is still responsive with `./hol-agent-helper.sh status`.

## Best Practices

1. **Always use temp files for backquoted terms** - Shell escaping is error-prone

2. **Check goal state frequently** - Use `p();` after each tactic to see current state

3. **Load theories early** - Load all needed theories at session start

4. **Use backup** - If a tactic takes you in the wrong direction, use `b();`

5. **Name your theorems** - Extract proved theorems with meaningful names for later use

6. **One command at a time** - Send tactics individually to see intermediate states

## Example: Complete Proof Session

```bash
# Start HOL
./hol-agent-helper.sh start

# Load theory
./hol-agent-helper.sh send 'open arithmeticTheory;'
```

Then for each step, write to `.hol_cmd.sml` and run `./hol-agent-helper.sh send:.hol_cmd.sml`:

```sml
(* Step 1: Set goal *)
g `!n. n + 0 = n`;

(* Step 2: Induction *)
e (Induct_on `n`);

(* Step 3: Base case - use simplification *)
e (simp []);

(* Step 4: Step case - use ADD_CLAUSES and assumption *)
e (asm_simp_tac bool_ss [ADD_CLAUSES]);

(* Step 5: Extract theorem *)
val add_zero_right = top_thm();
```

## Output Interpretation

HOL output includes ANSI color codes (e.g., `[0;32m`). These indicate:
- Variables are colored for readability
- The turnstile `⊢` separates assumptions from conclusion
- `thm` type indicates a proved theorem
- `proof` type indicates an ongoing proof

## Cleanup

When done, stop the HOL session:
```bash
./hol-agent-helper.sh stop
```
