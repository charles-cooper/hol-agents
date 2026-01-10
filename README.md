# HOL4 Proof Agents

Autonomous HOL4 theorem proving using Claude. Breaks proof development into three phases (planning, sketching, proving), each with specialized methodology.

## Quick Start

```bash
pip install -r requirements.txt

# Interactive (Claude Code with skills)
# /hol4-plan, /hol4-sketch, /hol4-prove

# Autonomous per-phase
python hol_planner.py --goal "prove theorem X"
python hol_sketch.py --plan plan.md --workdir /path
python hol_proof_agent.py --task TASK_foo.md

# End-to-end pipeline
python hol_pipeline.py --theorem X --workdir /path
```

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Entry Points                          │
│  Claude Code (TUI)  │  Python Wrappers  │  Pipeline     │
└─────────────────────┴───────────────────┴───────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────┐
│                 Methodology Prompts                      │
│    Planner         │    Sketcher       │   Prover       │
│   (Phase 1)        │   (Phase 2)       │  (Phase 3)     │
└─────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────┐
│                    MCP Server                            │
│  hol_start, hol_send, hol_cursor_*, holmake             │
└─────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────┐
│                HOL4 (hol --zero)                         │
│  Goaltree mode: gt, etq, p(), backup(), drop()          │
└─────────────────────────────────────────────────────────┘
```

## The Three Phases

### Phase 1: Planning

Create a rigorous mathematical argument for why a theorem is provable.

- Mathematical reasoning, NOT tactics
- Validate ALL assumptions against actual HOL4 definitions
- Spawn validation subagents to check claims
- Output: PROVABLE / NOT PROVABLE / UNKNOWN with full argument

```bash
python hol_planner.py --goal "prove enc_valid" --output plan.md
```

### Phase 2: Sketching

Translate the plan into HOL4 code structure with cheats.

- Split work into subtasks that fit in one context window
- Create SML files that COMPILE (with cheats)
- Every theorem needs "WHY THIS IS TRUE" comment
- Create TASK_*.md files for each cheat

```bash
python hol_sketch.py --plan plan.md --workdir /path/to/project
```

### Phase 3: Proving

Fill in cheats and complete proofs.

- Use goaltree mode (gt/etq) for tactic recording
- Use cursor tools for file-based workflow
- Run until holmake passes with no CHEAT warnings

```bash
python hol_proof_agent.py --task TASK_foo.md
```

## File Organization

```
prompts/hol4/
  planner.md              # Phase 1 methodology
  sketch_impl.md          # Phase 2 methodology
  proof_agent.template.md # Phase 3 methodology

skills/hol4/
  SKILL.md                # Skill index
  plan.md, sketch.md, prove.md  # TUI entry points

hol_mcp_server.py         # MCP server with HOL tools
hol_session.py            # HOL subprocess management
hol_cursor.py             # File-based proof cursor
hol_file_parser.py        # SML theorem parsing

hol_planner.py            # Phase 1 wrapper
hol_sketch.py             # Phase 2 wrapper
hol_proof_agent.py        # Phase 3 orchestrator
hol_pipeline.py           # End-to-end automation

repo_prompt/              # Detailed recovery prompts
legacy/                   # Previous bash-based implementation
```

## MCP Tools

### Session Management
- `hol_start(workdir, name)` - Start/reconnect HOL session (idempotent)
- `hol_sessions()` - List active sessions
- `hol_stop(session)` - Terminate session
- `hol_restart(session)` - Stop + start

### HOL Interaction
- `hol_send(session, command, timeout)` - Send SML code
- `hol_interrupt(session)` - SIGINT for runaway tactics
- `holmake(workdir, target, timeout)` - Run Holmake --qof

### Cursor Tools (recommended workflow)
- `hol_cursor_init(file, session)` - Parse file, enter goaltree at first cheat
- `hol_cursor_complete(session)` - Extract proof (agent splices into file)
- `hol_cursor_status(session)` - Show progress
- `hol_cursor_reenter(session)` - Set up goaltree for current theorem

## Interactive Usage (Claude Code)

Install the skill:
```bash
# From your project directory
/path/to/hol-agents/install-skill.sh

# Or manually
mkdir -p .claude/skills
ln -s /path/to/hol-agents/skills/hol4 .claude/skills/hol4
```

Then use `/hol4-plan`, `/hol4-sketch`, `/hol4-prove` to adopt each phase's methodology.

## CLI Options (hol_proof_agent.py)

```
--task, -t       Task file (required)
--claude-md, -c  CLAUDE.md path (auto-discovered)
--prompt, -p     Initial prompt override
--fresh          Ignore saved session state
--model, -m      Model (default: claude-sonnet-4-...)
--max-messages   Messages before handoff (default: 100)
```

## Key Design Decisions

- **HOL sessions survive handoffs** - MCP server persists across context clears
- **Prompts are source of truth** - Methodologies in prompts/, not code
- **All HOL via MCP** - Never direct Bash to HOL
- **Cursor workflow is primary** - init → (prove → complete) × N → done

## Agent File Management

[TaskManager.exe](https://pypi.org/project/taskmanager-exe/) is recommended for managing `.agent-files/` scratch space (task files, memory, status, handoffs).

## Requirements

- Python 3.10+
- HOL4 with `hol` in PATH
- fastmcp >= 2.0.0
- claude-agent-sdk >= 0.1.0

## License

MIT
