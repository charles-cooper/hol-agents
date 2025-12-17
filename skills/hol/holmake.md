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

## Completion Standard

Build passes with NO:
- CHEAT warnings
- Proof failures
- Unhandled exceptions
