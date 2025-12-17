# HOL4 Interactive Theorem Proving

You are a **subagent** doing ITP work. Do NOT delegate - do the work yourself.

## Critical: Backquotes

HOL backticks fail silently in shell. **Always use file method:**
```
echo 'g `!x. P x`;' > .hol_cmd_${HOL_SESSION_ID:-default}.sml
skills/hol/scripts/hol-agent-helper.sh send:.hol_cmd_${HOL_SESSION_ID:-default}.sml
```

## Helper Commands

```
start [DIR]      - start session (cwd default)
send 'code'      - send SML (no backquotes)
send:FILE        - send file (use for backquotes)
load-to FILE N   - load script to line N (recommended)
log              - show session log
status           - check if running
interrupt        - SIGINT (stop runaway tactic)
stop             - end session
```
Path: `skills/hol/scripts/hol-agent-helper.sh CMD`

**Session ID:** Always use `-s <id>` flag given in your prompt to avoid conflicts.

## load-to Workflow

**To blank line** (between theorems): loads deps, executes to LINE, interact via send.
**To cheat line**: loads to theorem, replays tactics to cheat, ready to prove.
Re-run load-to to reset. Handles `>-`/`THEN1` nesting.

## Files

`.hol_cmd_<session>.sml` - commands to send | `.hol_init.sml` - auto-loaded on start

## Goal Management

`g \`tm\`` set | `e(tac)` apply | `p()` print | `b()` back | `drop()` abandon | `top_thm()` extract | `r n` rotate

## Theorem Search

`DB.find "name"` | `DB.match [] \`\`pat\`\`` | `DB.theorems "thy"`

## Tactics

**Prefer:** `simp[thm]`, `gvs[AllCaseEqs()]`, `fs[]`, `drule_all thm`

| Tactic | Use |
|--------|-----|
| `Induct_on \`v\`` | induction |
| `Cases_on \`e\`` | case split |
| `rw[thms]`/`simp[]`/`gvs[]` | rewrite/simplify |
| `metis_tac[thms]` | first-order (slow, avoid large goals) |
| `irule thm` | apply implication |
| `drule thm`/`drule_all thm` | forward reasoning |
| `qexists_tac \`w\`` | existential witness |
| `conj_tac` | split conjunction |
| `strip_tac` | intro forall/implies |

**Combinators:** `>>` (THEN all), `>-` (THEN1 first only), `\\` (THEN)

## Patterns

- Case: `Cases_on \`x\` >> gvs[]`
- List induction: `Induct_on \`l\``
- Forward: `drule_all thm >> simp[]`
- Recursive defs: `simp[Once def]` not `fs[def]` (avoids blowup)

## Avoid

- `metis_tac` on large search space (hangs)
- `fs[recursive_def]` (blowup)
- Broad `simp[]` on complex goals

## sg / by / suffices_by

- `'tm' by tac` - prove tm, add as assumption (must close)
- `sg 'tm' >- tac` - tm as subgoal, tac must close it
- `'tm' suffices_by tac` - prove tm => goal

## Performance

- If tactic takes >15 seconds, abort and try different approach
- Test tactics individually before combining
- Use targeted rewrites, not broad simp calls
