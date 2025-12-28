# MCP Server Recovery Prompt

## File: `hol_mcp_server.py`

FastMCP server providing HOL4 interaction tools. In-memory session registry.

## Dependencies

- fastmcp >= 2.0.0
- hol_session.py (HOLSession class)
- hol_cursor.py (ProofCursor class)

## Session Registry

```python
_sessions: dict[str, SessionEntry]  # name -> entry

@dataclass
class SessionEntry:
    session: HOLSession
    started: datetime
    workdir: Path
    cursor: ProofCursor | None
    holmake_env: dict | None  # cached env vars
```

In-memory only. Sessions survive across Claude context clears (handoffs) but not server restarts.

## Tools

### Session Management

```python
@mcp.tool()
def hol_start(workdir: str, name: str = "default") -> str:
    """Start or reconnect HOL session. Idempotent.

    If session exists and running: return top_goals()
    If session exists but dead: restart it
    If new: create session, start HOL, return greeting
    """

@mcp.tool()
def hol_sessions() -> str:
    """List active sessions: name, workdir, age, status (running/dead)"""

@mcp.tool()
def hol_send(session: str, command: str, timeout: int = 5) -> str:
    """Send SML command, return output. Max timeout 600s.

    Handles timeout by calling interrupt().
    """

@mcp.tool()
def hol_interrupt(session: str) -> str:
    """Send SIGINT to abort runaway tactic."""

@mcp.tool()
def hol_stop(session: str) -> str:
    """SIGTERM + wait. Removes from registry."""

@mcp.tool()
def hol_restart(session: str) -> str:
    """Stop + start. Preserves workdir."""
```

### Build

```python
@mcp.tool()
def holmake(workdir: str, target: str = "", timeout: int = 90) -> str:
    """Run Holmake --qof in workdir.

    Max timeout 1800s.
    On failure: return output + contents of .hollogs/*.log
    Caches env vars (HOLDIR, etc.) for reuse.
    """
```

### Cursor Tools (Recommended Entry Point)

```python
@mcp.tool()
def hol_cursor_init(file: str, session: str = "default", workdir: str = None) -> str:
    """Initialize cursor-based workflow.

    1. Auto-start session if needed
    2. Parse file for theorems/cheats
    3. Load HOL context up to first cheat
    4. Enter goaltree for first cheat
    5. Return top_goals() output
    """

@mcp.tool()
def hol_cursor_complete(session: str) -> str:
    """Complete current theorem, advance to next.

    1. Extract proof via p()
    2. Splice tactics into file (replace cheat)
    3. Advance to next cheat
    4. Enter goaltree for next theorem
    5. Return new top_goals()
    """

@mcp.tool()
def hol_cursor_status(session: str) -> str:
    """Show progress: file, position, current theorem, remaining cheats."""

@mcp.tool()
def hol_cursor_reenter(session: str) -> str:
    """Re-enter goaltree after drop() or to retry current theorem."""
```

## Key Behaviors

1. **Idempotent hol_start**: Calling repeatedly is safe, returns current state
2. **Session names are explicit**: Not derived from directory
3. **Cursor is optional**: Can use hol_send directly for manual control
4. **holmake caches env**: Avoids repeated PATH discovery
5. **Timeout handling**: Long-running tactics get interrupted, not hung

## Reconstruction Notes

- Use FastMCP's `@mcp.tool()` decorator pattern
- Session registry is a module-level dict
- HOL subprocess owned by HOLSession, not MCP server
- Cursor stored in SessionEntry, created on cursor_init
