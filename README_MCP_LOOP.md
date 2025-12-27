# HOL4 Proof Agent (MCP Architecture)

Autonomous HOL4 theorem proving agent using Claude Agent SDK + MCP server.

## Architecture

```
hol_proof_agent.py (orchestrator)
       ↓ spawns via claude-agent-sdk
Claude Code CLI (with MCP server)
       ↓ MCP protocol (stdio)
hol_mcp_server.py (in-memory session registry)
       ↓ owns subprocess (stdin/stdout pipes)
HOL4 (hol --zero)
```

## Quick Start

```bash
pip install -r requirements.txt
python hol_proof_agent.py --task path/to/TASK_foo.md
```

## Files

| File | Purpose |
|------|---------|
| `hol_proof_agent.py` | Orchestrator - runs forever until PROOF_COMPLETE |
| `hol_mcp_server.py` | MCP server exposing HOL tools |
| `hol_session.py` | HOLSession class (async subprocess, null-byte framing) |
| `hol_cursor.py` | ProofCursor for multi-theorem files |
| `hol_file_parser.py` | SML parsing (TheoremInfo, splice_into_theorem) |

## MCP Tools

### Session Management
- `hol_start(workdir, name)` - Start new HOL session
- `hol_sessions()` - List active sessions
- `hol_attach(session)` - Attach to existing session
- `hol_stop(session)` - Terminate session

### HOL Interaction
- `hol_send(session, command, timeout)` - Send SML code
- `hol_proof_state(session)` - Get current goals (p() + top_goals())
- `hol_interrupt(session)` - Abort runaway tactic (SIGINT)
- `holmake(workdir, target)` - Run Holmake --qof

### Cursor Tools (multi-theorem files)
- `hol_cursor_init(session, file)` - Parse file, position at first cheat
- `hol_cursor_status(session)` - Get current position
- `hol_cursor_start(session)` - Enter goaltree mode for current theorem
- `hol_cursor_complete(session)` - Splice proof into file, advance

## CLI Options

```
--task, -t       Task file (required)
--claude-md, -c  CLAUDE.md path (auto-discovered)
--prompt, -p     Initial prompt
--fresh          Ignore saved session state
--model, -m      Model (default: claude-opus-4-20250514)
--max-messages   Messages before handoff (default: 100)
```

## Session Lifecycle

Sessions are **in-memory only**:
- Survive within single MCP server lifetime (including handoffs)
- Do NOT survive orchestrator restarts
- State file (`.claude/hol_agent_state.json`) tracks Claude session, not HOL

## Handoff Mechanism

At `--max-messages` threshold:
1. Agent commits progress (git add specific files)
2. Captures proof state via `hol_proof_state()`
3. Updates task file with `## Handoff` section
4. Clears Claude session (new context)
5. Same MCP server continues → HOL session preserved

## Interrupt Handling

- Ctrl+C: Save state, prompt for input
- Enter message to send to Claude
- Empty to continue
- 'q' to quit

## Completion

Agent outputs `PROOF_COMPLETE: <summary>` when:
- `holmake(workdir)` passes (exit 0)
- No CHEAT warnings in output
- No FAIL in output

## Legacy

`hol-agent-helper.sh` is the previous bash-based implementation (superseded).
