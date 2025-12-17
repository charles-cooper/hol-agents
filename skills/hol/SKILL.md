---
name: hol
description: HOL4 interactive proof development. Use when working with HOL4 proofs, .sml theorem files, Holmake builds, or hol-agent-helper.sh sessions.
---

# HOL4 Proof Development

## Completion Standard

Task NOT complete until: all cheats removed, build passes with no CHEAT warnings.
**Documenting remaining work is NOT completion** - do the work or hit a genuine blocker.

## Critical: Backquotes

HOL backticks fail silently in shell. **Always use file method:**
```
echo 'g `!x. P x`;' > .hol_cmd_${HOL_SESSION_ID:-default}.sml
.claude/skills/hol/scripts/hol-agent-helper.sh send:.hol_cmd_${HOL_SESSION_ID:-default}.sml
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
Path: `.claude/skills/hol/scripts/hol-agent-helper.sh CMD`

**Multiple sessions:** Use `-s name` flag or `HOL_SESSION_ID=name` env var for concurrent sessions in same directory.

## load-to Workflow

**To blank line** (between theorems): loads deps, executes to LINE, interact via send.
**To cheat line**: loads to theorem, replays tactics to cheat, ready to prove.
Re-run load-to to reset. Handles `>-`/`THEN1` nesting.

## Files

`.hol_cmd_${HOL_SESSION_ID:-default}.sml` - commands to send | `.hol_init.sml` - auto-loaded on start | `.hol_test.sml` - scratch
Check `.hol_init.sml` before issuing commands to avoid duplicates.

## Goal Management

`g \`tm\`` set | `e(tac)` apply | `p()` print | `b()` back | `drop()` abandon | `top_thm()` extract | `r n` rotate

## Theorem Search

`DB.find "name"` | `DB.match [] \`\`pat\`\`` | `DB.theorems "thy"`

## Tactics

**Prefer:** `simp[thm]`, `gvs[AllCaseEqs()]`, `fs[]`, `drule_all thm`, `FIRST[t1,t2]`

| Tactic | Use |
|--------|-----|
| `Induct_on \`v\`` | induction |
| `Cases_on \`e\`` | case split |
| `rw[thms]`/`simp[]`/`gvs[]` | rewrite/simplify |
| `metis_tac[thms]` | first-order (slow, avoid large goals) |
| `irule thm` | apply implication |
| `drule thm`/`drule_all thm` | forward reasoning |
| `qexists_tac \`w\`` | existential witness |
| `conj_tac` | split ∧ goal |
| `strip_tac` | intro ∀/⇒ |

**Combinators:** `>>` (THEN all), `>-` (THEN1 first only), `>|` (parallel: `tac >| [t1,t2]`), `\\` (THEN)

## Patterns

- Case: `Cases_on \`x\` >> gvs[]`
- List induction: `Induct_on \`l\``
- Mutual recursion: `ho_match_mp_tac fn_ind`
- Forward: `drule_all thm >> simp[]` (better than irule for instantiation)
- Recursive defs: `simp[Once def]` not `fs[def]` (avoids blowup)
- Unfold assumption: `qpat_x_assum \`pat\` mp_tac >> simp[Once def] >> strip_tac`
- RHS only: `CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [def]))`

## Avoid

- `rpt metis_tac[...]` on many subgoals (exponential)
- `metis_tac` on large search space (hangs)
- `fs[recursive_def]` (blowup)

## sg / by / suffices_by

- `'tm' by tac` - prove tm, add as assumption (must close)
- `sg 'tm' >- tac` - tm as subgoal, tac must close it
- `sg 'tm' >> tac` - tm as subgoal, tac applies to ALL goals
- `'tm' suffices_by tac` - prove tm ⇒ goal

Error "first subgoal not solved" = tac didn't close tm.

## Debugging

- `fn`, `f` conflict with HOL - use `func`
- Pair: `Cases_on \`f args\` >> fs[]`
- irule fails: try `drule_all`
- metis_tac fails: use `gvs[]` or `first_x_assum irule >> simp[]`

## Troubleshooting

Parse error → check backquotes, theory loaded | Hangs → `interrupt` or re-run `load-to` | Wrong state → `load-to` resets

**Tip:** Send tactics individually to see intermediate states.
