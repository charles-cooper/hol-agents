# HOL4 Proof Agents - Contributor Guide

This document explains the internals for contributors and AI agents working on this codebase.

## Repository Structure

```
prompts/hol4/           # Methodology prompts (SOURCE OF TRUTH)
  planner.md            # Phase 1: mathematical planning
  sketch_impl.md        # Phase 2: HOL4 sketching with cheats
  proof_agent.template.md  # Phase 3: filling in cheats

skills/hol4/            # Claude Code TUI entry points
  SKILL.md              # Skill index
  plan.md, sketch.md, prove.md

repo_prompt/            # Detailed recovery prompts for reconstruction
  MAIN.md               # Architecture overview
  mcp_server.md, session.md, cursor.md, ...

hol_mcp_server.py       # MCP server (FastMCP)
hol_session.py          # HOL subprocess wrapper
hol_cursor.py           # File-based proof cursor
hol_file_parser.py      # SML parsing

hol_planner.py          # Phase 1 orchestrator
hol_sketch.py           # Phase 2 orchestrator
hol_proof_agent.py      # Phase 3 orchestrator (forever loop)
hol_pipeline.py         # End-to-end automation

sml_helpers/etq.sml     # Tactic extraction for goaltree mode
tests/                  # Python tests for MCP components
legacy/                 # Old bash-based implementation
```

## Key Components

### MCP Server (`hol_mcp_server.py`)

FastMCP server providing HOL4 tools. In-memory session registry.

**Session registry:** `dict[str, tuple[HOLSession, datetime, Path, ProofCursor|None]]`

**Tools:**
- Session: `hol_start`, `hol_send`, `hol_interrupt`, `hol_stop`, `hol_restart`, `hol_sessions`
- Cursor: `hol_cursor_init`, `hol_cursor_complete`, `hol_cursor_status`, `hol_cursor_reenter`
- Build: `holmake`

**Key detail:** The MCP server is imported (not spawned) by orchestrators. This allows sessions to survive across Claude context clears (handoffs).

### HOL Session (`hol_session.py`)

Async subprocess wrapper for HOL4.

**Null-byte framing:** HOL started with `--zero` flag. Each response terminated by `\0`. The `send()` method writes command + NUL, reads until NUL.

**Process group:** Uses `setsid` to create new process group. Enables clean interrupt (`os.killpg`) without killing parent.

**Init scripts:** Loads `sml_helpers/etq.sml` (tactic extraction) and `.hol_init.sml` (project-specific) on startup.

**Interrupt handling:** HOL `--zero` mode outputs TWO null bytes after SIGINT. First terminates interrupt message, second is spurious. Must drain both.

### Proof Cursor (`hol_cursor.py`, `hol_file_parser.py`)

Tracks position in an SML file, manages proof lifecycle.

**Workflow:** `init → (prove until no goals → complete) × N`

1. `initialize(file)` - Parse file, find first cheat
2. `start_current()` - Load context, enter goaltree for current theorem
3. `complete_and_advance()` - Internally calls p(), splices into file, moves to next cheat. Do NOT drop() or edit file manually before calling.

**Splicing:** `splice_into_theorem(content, theorem_name, tactics)` replaces the proof body while preserving structure.

**Goaltree mode:** Uses `gt`/`etq`/`p()` instead of goalstack. `etq` records tactic names, `p()` extracts the proof script.

### Orchestrators

**`hol_proof_agent.py`** (Phase 3 - full):
- Forever loop until `PROOF_COMPLETE:` detected
- Handoff at `--max-messages`: commit, update task file, clear Claude session
- HOL session survives handoffs (same MCP server)
- Auto-injects HOL state (sessions, goals, holmake) at startup
- Bash restricted to git commands only

**`hol_planner.py`** (Phase 1 - thin):
- Loads planner prompt as system prompt
- Runs until `PLAN_COMPLETE:`
- No MCP needed (pure reasoning)

**`hol_sketch.py`** (Phase 2 - thin):
- Loads sketch prompt as system prompt
- MCP for holmake verification
- Runs until `SKETCH_COMPLETE:`

**`hol_pipeline.py`** (chains all three):
- Plan → Sketch → Prove
- `--skip-plan`, `--skip-sketch` for partial runs

## Goaltree Mode

Always use goaltree (`gt`/`etq`) instead of goalstack (`g`/`e`):

```sml
gt `A /\ B ==> B /\ A`;
etq "strip_tac";
etq "conj_tac";
etq "simp[]";
etq "simp[]";
p();  (* Shows: strip_tac \\ conj_tac >- simp[] >- simp[] *)
```

**Why:** `etq` records tactic names as strings, enabling `p()` to extract the exact proof script. Regular `e()` loses this information.

**Backtracking:** `backup()` removes last tactic from tree. `drop()` abandons proof entirely.

## State Persistence

**Agent state:** `.claude/hol_agent_state.json`
```json
{
  "session_id": "...",           // Claude SDK session (for resume)
  "message_count": 42,           // Total across handoffs
  "hol_session": "default",      // HOL session name in MCP registry
  "holmake_env": {...}           // Cached env vars
}
```

**HOL sessions:** In-memory only (MCP server). Survive handoffs, NOT orchestrator restarts.

## Testing

```bash
# Unit tests
python -m pytest tests/

# Manual MCP test
python hol_mcp_server.py  # Starts MCP server on stdio
```

## Gotchas

1. **Null-byte framing:** HOL `--zero` mode is essential. Without it, can't reliably detect response boundaries.

2. **Double null after interrupt:** Must drain both or next `send()` returns empty.

3. **MCP import vs spawn:** Orchestrators import the MCP server module to share the session registry. Spawning would create isolated registries.

4. **Cursor vs proof state:** Two orthogonal concerns:
   - File position (ProofCursor): which theorem in file
   - Proof state (HOL goaltree): which step in current proof

5. **Template placeholders:** `proof_agent.template.md` has `{mcp}`, `{max_agent_messages}`, `{claude_md}` that orchestrator fills in.

6. **etq.sml loading:** Session must load `sml_helpers/etq.sml` for `etq` to work. Done automatically in `HOLSession.start()`.

## Extending

**Adding a new MCP tool:**
1. Add function in `hol_mcp_server.py` with `@mcp.tool()` decorator
2. Document in `repo_prompt/mcp_server.md`
3. Update prompts if agents should use it

**Adding a new phase:**
1. Create methodology prompt in `prompts/hol4/`
2. Create thin wrapper in `hol_<phase>.py`
3. Add to pipeline in `hol_pipeline.py`
4. Create skill in `skills/hol4/`

**Changing methodology:**
Edit the prompt files. They are the source of truth. The Python code is just infrastructure.

## Recovery

If codebase is lost, see `repo_prompt/MAIN.md` for full architecture and component-specific recovery prompts.
