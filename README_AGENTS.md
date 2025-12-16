# HOL4 Agent Helper - Usage Guide

## Critical: Backquotes

HOL uses backticks for terms (`` `!x. P x` ``). Shell escaping fails silently.

**Always use file method:** write to `.hol_cmd.sml`, run `send:.hol_cmd.sml`

## Commands

| Command | Description |
|---------|-------------|
| `start [DIR]` | Start HOL session (default: current dir) |
| `send 'code'` | Send simple SML (no backquotes) |
| `send:FILE` | Send file contents (use for backquotes) |
| `status` | Check if session running |
| `status:DIR` | Check session for specific dir |
| `log` | Show full session log |
| `load-to FILE LINE` | Load script to LINE (recommended) |
| `interrupt` | Send SIGINT to stop runaway tactic |
| `stop` | Stop session |
| `cleanup` | Kill ALL sessions (nuclear) |

All commands: `~/hol-agents/hol-agent-helper.sh CMD`

## Workflow: load-to

Recommended approach for working on existing scripts.

### To a blank line (between theorems)

1. Find blank line after block ender (`QED`/`End`/`;`)
2. Run `load-to /path/to/script.sml LINE`
   - Auto-discovers and loads dependencies
   - Executes script up to LINE
3. Interact via `send`/`send:FILE`
4. Re-run `load-to` to reset session

### To a cheat (inside a proof)

1. Find line containing `cheat`
2. Run `load-to /path/to/script.sml LINE`
   - Loads script up to theorem
   - Sets goal, replays tactics to cheat point
3. Session ready at the cheat - prove the goal
4. Handles `>-`/`THEN1` nesting automatically

## HOL Reference

### Goal Management

```
g `term`;     -- set goal
e(tactic);    -- apply tactic
p();          -- print current goal
b();          -- backup one step
drop();       -- abandon proof
top_thm();    -- extract proved theorem
r n;          -- rotate to subgoal n
```

### Common Tactics

| Tactic | Example |
|--------|---------|
| `Induct_on` | ``e(Induct_on `n`);`` |
| `Cases_on` | ``e(Cases_on `x`);`` |
| `rw` | `e(rw[thm1,thm2]);` |
| `simp` | `e(simp[]);` |
| `gvs` | `e(gvs[]);` |
| `metis_tac` | `e(metis_tac[thms]);` |
| `irule` | `e(irule thm);` |
| `drule` | `e(drule thm);` |
| `qexists_tac` | ``e(qexists_tac `witness`);`` |
| `conj_tac` | `e conj_tac;` (split conjunction goal) |
| `strip_tac` | `e strip_tac;` (intro forall/implies) |
| `CCONTR_TAC` | `e CCONTR_TAC;` (contradiction) |

Combinators: `tac1 \\ tac2` (THEN), `tac1 >- tac2` (THEN1)

### Theorem Search

```
DB.find "ADD";              -- by name substring
DB.match [] ``_ + 0``;      -- by pattern
DB.theorems "arithmetic";   -- list theory
```

## Troubleshooting

| Problem | Solution |
|---------|----------|
| Parse error / field not registered | Check backquotes, ensure theory loaded |
| Tactic fails | `p();` to see goal, try different tactic |
| Session hangs | `interrupt`, or re-run `load-to` |
| Timeout (5min) | `status` to check, `load-to` to reset |
| Wrong session state | `load-to` always resets cleanly |

Tip: Send tactics individually to see intermediate goal states.
