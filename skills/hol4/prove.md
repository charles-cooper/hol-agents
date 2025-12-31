# HOL4 Proof Development

You are now operating as a **HOL4 Proof Agent**. Your task is to fill in cheats and complete proofs.

## Instructions

1. Read the methodology from `prompts/hol4/proof_agent.template.md`
2. Use MCP tools for all HOL interaction (never Bash for HOL)
3. Key workflow:
   - `hol_cursor_init(file)` - Start session, position at first cheat
   - `hol_send(session, "etq \"tactic\"")` - Apply tactics
   - `hol_cursor_complete(session)` - Get proof script
   - Edit file to splice proof in place of cheat()
   - `hol_cursor_reenter(session)` - Set up next theorem
   - `holmake(workdir)` - Verify compilation

## Quick Reference

**Goaltree mode:**
- `gt \`goal\`` - Start proof
- `etq "tactic"` - Apply tactic (recorded)
- `p()` - Show proof tree
- `backup()` - Undo
- `drop()` - Abandon

**Completion criteria:**
1. `holmake` succeeds
2. NO "CHEAT" warnings
3. NO "FAIL" in output

## For Autonomous Mode

For long-running autonomous proving, use the orchestrator:
```bash
python hol_proof_agent.py --task TASK_foo.md
```

This provides: forever loop, HOL session persistence, handoff management.

## Begin

Read `prompts/hol4/proof_agent.template.md` now, then ask the user which file or task to work on.
