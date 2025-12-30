# HOL4 Agents - Repository Specification

This document specifies the design of this repository such that it can be recreated by an AI agent. It captures intent and architecture, not implementation details.

## Purpose

Autonomous HOL4 theorem proving using Claude as the reasoning engine. The system breaks proof development into three phases, each with its own methodology, and can run interactively or fully automated.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                      User Interface                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │ Claude Code  │  │   Python     │  │   Pipeline   │       │
│  │    (TUI)     │  │  Wrappers    │  │   Script     │       │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘       │
└─────────┼─────────────────┼─────────────────┼───────────────┘
          │                 │                 │
          ▼                 ▼                 ▼
┌─────────────────────────────────────────────────────────────┐
│                    Methodology Prompts                       │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │   Planner    │  │   Sketcher   │  │ Proof Agent  │       │
│  │  (Phase 1)   │  │  (Phase 2)   │  │  (Phase 3)   │       │
│  └──────────────┘  └──────────────┘  └──────────────┘       │
└─────────────────────────────────────────────────────────────┘
          │                 │                 │
          ▼                 ▼                 ▼
┌─────────────────────────────────────────────────────────────┐
│                      MCP Server                              │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  hol_start, hol_send, hol_interrupt, holmake         │   │
│  │  hol_cursor_init, hol_cursor_complete, ...           │   │
│  └──────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                    HOL4 Process                              │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  hol --zero (null-byte framing)                      │   │
│  │  Goaltree mode: gt, etq, p(), backup(), drop()       │   │
│  │  (No rotate() - always works on leftmost goal)       │   │
│  └──────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

## The Three Phases

### Phase 1: Planning

**Purpose:** Create a rigorous mathematical argument for why a theorem is provable.

**Key requirements:**
- Mathematical reasoning, NOT tactics
- Validate ALL assumptions against actual definitions
- Spawn validation subagents to check claims
- Terminate only when ZERO unverified assumptions remain
- Output: PROVABLE / NOT PROVABLE / UNKNOWN verdict with full argument

**Methodology prompt:** `prompts/hol4/planner.md`

### Phase 2: Sketching

**Purpose:** Translate the plan into HOL4 code structure with cheats.

**Key requirements:**
- Split work into subtasks that fit in one context window
- Create SML files that COMPILE (with cheats)
- Every theorem needs "WHY THIS IS TRUE" comment preserving planner's argument
- Create TASK_*.md files for each cheat (self-contained subagent prompts)
- Verify compilation with holmake

**Methodology prompt:** `prompts/hol4/sketch_impl.md`

**Outputs:**
- `*_sketch.sml` - Compilable HOL4 showing proof structure
- `TASK_*.md` - One per cheat, contains goal + argument + resources + approach

### Phase 3: Proving

**Purpose:** Fill in cheats and complete proofs.

**Key requirements:**
- Use goaltree mode (gt/etq) for tactic recording and extraction
- Use cursor tools for file-based workflow
- Run until holmake passes with no CHEAT warnings
- Can run forever with handoff management for long proofs

**Methodology prompt:** `prompts/hol4/proof_agent.template.md`

## Key Components

### MCP Server (`hol_mcp_server.py`)

Provides tools for HOL4 interaction via MCP protocol:

**Session management:**
- `hol_start(workdir, name)` - Start/reconnect session (idempotent)
- `hol_send(session, command, timeout)` - Send SML, get output
- `hol_interrupt(session)` - SIGINT for runaway tactics
- `hol_stop(session)` / `hol_restart(session)`
- `hol_sessions()` - List active sessions

**Cursor tools (recommended workflow):**
- `hol_cursor_init(file, session)` - Parse file, position at first cheat, enter goaltree
- `hol_cursor_complete(session)` - Extract p(), splice into file, advance to next
- `hol_cursor_status(session)` - Show progress
- `hol_cursor_reenter(session)` - Re-enter goaltree after drop()

**Build:**
- `holmake(workdir, target, timeout)` - Run Holmake, return output

### HOL Session (`hol_session.py`)

Manages HOL4 subprocess:
- Spawns `hol --zero` with null-byte framing
- Loads helper scripts (etq.sml for tactic extraction)
- Handles timeout with interrupt
- Process group management for clean shutdown

### Proof Cursor (`hol_cursor.py`, `hol_file_parser.py`)

Tracks position in an SML file:
- Parses theorems, identifies cheats
- Loads context up to current theorem
- Splices completed proofs back into file
- Advances through file theorem by theorem

### Orchestrators

**`hol_proof_agent.py`** - Full orchestrator for Phase 3:
- Forever loop until PROOF_COMPLETE
- HOL session persistence across context clears (handoffs)
- Auto-injects HOL state at startup
- Bash restricted to git only (forces MCP usage)
- Usage/cost tracking

**`hol_planner.py`** - Thin wrapper for Phase 1:
- Loads planner prompt as system prompt
- Runs until PLAN_COMPLETE
- No MCP needed (pure reasoning)

**`hol_sketch.py`** - Thin wrapper for Phase 2:
- Loads sketch prompt as system prompt
- Has MCP access for holmake verification
- Runs until SKETCH_COMPLETE

**`hol_pipeline.py`** - Chains all three phases:
- Plan → Sketch → Prove for each task file
- Supports --skip-plan, --skip-sketch for partial runs

### Skills (TUI entry points)

For interactive use in Claude Code:
- `/hol4-plan` - Injects planner methodology
- `/hol4-sketch` - Injects sketch methodology
- `/hol4-prove` - Injects prover methodology

Skills reference the methodology prompts, providing a quick way to adopt the role in an interactive session.

## File Organization

```
prompts/hol4/
  planner.md              # Phase 1 methodology
  sketch_impl.md          # Phase 2 methodology
  proof_agent.template.md # Phase 3 methodology (template with {placeholders})

skills/hol4/
  SKILL.md                # Skill index
  plan.md                 # /hol4-plan entry point
  sketch.md               # /hol4-sketch entry point
  prove.md                # /hol4-prove entry point

hol_mcp_server.py         # MCP server with HOL tools
hol_session.py            # HOL subprocess management
hol_cursor.py             # File-based proof cursor
hol_file_parser.py        # SML theorem parsing

hol_planner.py            # Phase 1 autonomous wrapper
hol_sketch.py             # Phase 2 autonomous wrapper
hol_proof_agent.py        # Phase 3 full orchestrator
hol_pipeline.py           # End-to-end automation

sml_helpers/
  etq.sml                 # Tactic extraction helpers for goaltree mode
```

## Usage Patterns

### Interactive (Claude Code)
```
User: /hol4-plan
User: Plan the proof for theorem enc_valid in contractABIScript.sml
[... interactive planning session ...]

User: /hol4-sketch
User: Implement this plan
[... interactive sketching session ...]

User: /hol4-prove
User: Fill in TASK_enc_valid_base.md
[... interactive proving session ...]
```

### Autonomous per-phase
```bash
python hol_planner.py --goal "prove enc_valid" --output plan.md
python hol_sketch.py --plan plan.md --workdir /path/to/project
python hol_proof_agent.py --task TASK_foo.md
```

### End-to-end
```bash
python hol_pipeline.py --theorem enc_valid --workdir /path/to/project
```

## Key Invariants

1. **HOL sessions survive handoffs** - MCP server persists sessions across context clears
2. **Prompts are source of truth** - Methodologies live in prompts/, not scattered in code
3. **All HOL interaction via MCP** - Never direct Bash to HOL
4. **Cursor workflow is primary** - init → (prove → complete) × N → done
5. **Each phase is independently runnable** - User can control any phase manually

## Detailed Component Recovery Prompts

For implementation details sufficient to reconstruct each component:

| Component | Recovery Prompt |
|-----------|-----------------|
| MCP Server | [mcp_server.md](mcp_server.md) - Tools, session registry, cursor tools |
| HOL Session | [session.md](session.md) - Subprocess, null-byte framing, interrupt |
| Proof Cursor | [cursor.md](cursor.md) - File parsing, splicing, tactic extraction |
| Proof Agent | [proof_agent.md](proof_agent.md) - Forever loop, handoffs, state |
| Planner | [planner.md](planner.md) - Thin wrapper for phase 1 |
| Sketch | [sketch.md](sketch.md) - Thin wrapper for phase 2 |
| Pipeline | [pipeline.md](pipeline.md) - End-to-end automation |

## Recreating This Repository

**Order of implementation:**

1. **HOL Session** ([session.md](session.md))
   - Null-byte framing with `hol --zero`
   - Process group isolation for interrupt
   - Load etq.sml for tactic extraction

2. **MCP Server** ([mcp_server.md](mcp_server.md))
   - Session registry (in-memory dict)
   - Tools: hol_start, hol_send, hol_interrupt, holmake
   - Cursor tools: init, complete, status, reenter

3. **Proof Cursor** ([cursor.md](cursor.md))
   - Parse SML for Theorem/Triviality/Definition
   - Track cheats, splice completed proofs
   - Context loading for mid-file theorems

4. **Methodology Prompts** (see `prompts/hol4/*.md`)
   - Planner: mathematical rigor, validation subagents
   - Sketch: hierarchical decomposition, task files
   - Prover: goaltree workflow, complexity management

5. **Orchestrators** ([proof_agent.md](proof_agent.md), [planner.md](planner.md), [sketch.md](sketch.md))
   - Proof agent: forever loop, handoffs, state persistence
   - Planner/Sketch: thin wrappers, bounded tasks

6. **Pipeline** ([pipeline.md](pipeline.md))
   - Chain phases: Plan → Sketch → Prove
   - Support partial runs

7. **Skills** (see `skills/hol4/*.md`)
   - TUI entry points for interactive use

**The methodology prompts are the core IP** - they encode the proof development process. The infrastructure provides different ways to execute them.
