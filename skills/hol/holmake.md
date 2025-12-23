# Holmake Build Reference

You are a **subagent** doing build work. Do NOT delegate - do the work yourself.

## Running Builds

```bash
cd <theory_dir> && Holmake 2>&1 | tail -80
```

## Interpreting Output

**Success:** Theory compiles, shows "Saved theorem" messages, no errors.

**CHEAT warning:** Proof uses `cheat` - NOT complete until removed.

**Proof failure patterns:**
- `first subgoal not solved` - tactic didn't close subgoal
- `functions on lhs and rhs differ` - AP_TERM_TAC on mismatched functions
- `Exception raised at` - tactic threw exception

**Syntax errors:** Usually backquote issues or missing opens.

## Finding Failures

Check the log for details:
```bash
tail -100 <theory_dir>/.hol/logs/<TheoryName>
```

## Common Fixes

| Error | Likely Fix |
|-------|------------|
| `first subgoal not solved` | Tactic too weak, try `fs[]` instead of `simp[]` |
| Parse error with backticks | Check Unicode quotes vs ASCII |
| Theorem not found | Check theory loaded, spelling |
| Type mismatch | Check type annotations |

## Clean Build

```bash
cd <theory_dir> && Holmake cleanAll && Holmake
```

## Long-Running Builds

If build takes >2 minutes, kill YOUR running Holmake command (the Bash tool supports this).
Do NOT background the task or spawn separate kill commands.

Common causes of slow builds:
- `metis_tac` on large search space
- Unbounded `simp[]` or `fs[]` on recursive definitions
- Type inference on complex polymorphic terms

After killing, check the log to identify which proof is slow, then fix interactively.

## Completion Standard

Build passes with NO:
- CHEAT warnings
- Proof failures
- Unhandled exceptions
