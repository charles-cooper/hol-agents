"""Proof cursor for navigating through theorems without reloading."""

import asyncio
import os
import tempfile
from pathlib import Path

from hol_file_parser import TheoremInfo, parse_file, splice_into_theorem, parse_p_output
from hol_session import HOLSession, HOLDIR, escape_sml_string


def _parse_sml_string(output: str) -> str:
    """Extract string value from SML output like 'val it = "...": string'.

    Returns the raw escaped content - DO NOT unescape, as we pass this
    directly to another SML string literal (etq).
    """
    for line in output.split('\n'):
        line = line.strip()
        if line.startswith('val it = "'):
            # Handle both 'val it = "...": string' and 'val it = "..." : string'
            for suffix in ['": string', '" : string']:
                if suffix in line:
                    start = line.index('"') + 1
                    end = line.rindex(suffix)
                    return line[start:end]  # Keep SML escaping intact
    return ""


def _is_hol_error(output: str) -> bool:
    """Check if HOL output indicates an actual error (not just a warning).

    Returns True for real errors like:
    - SML exceptions ("Exception-", "raised exception")
    - HOL errors ("HOL_ERR")
    - Poly/ML errors ("poly: : error:")
    - Tactic failures ("Fail ")
    - TIMEOUT strings from HOL session

    Returns False for:
    - HOL warnings/messages ("<<HOL message:", "<<HOL warning:")
    - The word "error" appearing in goal terms (e.g., "error_state")
    """
    if output.startswith("TIMEOUT"):
        return True
    if output.lstrip().startswith("ERROR:") or output.lstrip().startswith("Error:"):
        return True
    if "Exception" in output:
        return True
    if "HOL_ERR" in output:
        return True
    if "poly: : error:" in output.lower():
        return True
    if "raised exception" in output.lower():
        return True
    # Tactic Fail with message
    if "\nFail " in output or output.startswith("Fail "):
        return True
    return False


async def get_script_dependencies(script_path: Path) -> list[str]:
    """Get dependencies using holdeptool.exe.

    Raises FileNotFoundError if holdeptool.exe doesn't exist.
    """
    holdeptool = HOLDIR / "bin" / "holdeptool.exe"
    if not holdeptool.exists():
        raise FileNotFoundError(f"holdeptool.exe not found at {holdeptool}")

    proc = await asyncio.create_subprocess_exec(
        str(holdeptool), str(script_path),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )
    stdout, stderr = await proc.communicate()
    if proc.returncode != 0:
        raise RuntimeError(f"holdeptool.exe failed: {stderr.decode()}")

    return [line.strip() for line in stdout.decode().splitlines() if line.strip()]


def get_executable_content(content: str, up_to_line: int) -> str:
    """Extract SML content from script up to specified line.

    Returns content from line 1 to up_to_line-1, including any
    Theory/Ancestors/Libs header (which sets up the environment).
    """
    lines = content.split('\n')
    prefix_lines = lines[:up_to_line - 1]
    return '\n'.join(prefix_lines)


def atomic_write(path: Path, content: str) -> None:
    """Write content to file atomically via temp file + rename."""
    fd, tmp_path = tempfile.mkstemp(dir=path.parent, suffix=".tmp", prefix=path.name)
    try:
        os.write(fd, content.encode())
        os.close(fd)
        Path(tmp_path).replace(path)
    except Exception:
        os.close(fd)
        Path(tmp_path).unlink(missing_ok=True)
        raise

class ProofCursor:
    """Track position in file, advance through theorems without reloading."""

    def __init__(self, source_file: Path, session: HOLSession):
        self.file = source_file
        self.session = session
        self.theorems: list[TheoremInfo] = []
        self.position: int = 0
        self.completed: set[str] = set()
        self._loaded_to_line: int = 0  # Track how much content is loaded
        self._file_mtime: float = 0.0  # mtime when file was parsed

    def _check_stale(self) -> bool:
        """Return True if file has been modified since last parse."""
        try:
            return self.file.stat().st_mtime != self._file_mtime
        except OSError:
            return True  # File gone = stale

    def current(self) -> TheoremInfo | None:
        """Get current theorem."""
        if 0 <= self.position < len(self.theorems):
            return self.theorems[self.position]
        return None

    def next(self) -> TheoremInfo | None:
        """Advance to next theorem."""
        if self.position + 1 < len(self.theorems):
            self.position += 1
            return self.current()
        return None

    def next_cheat(self) -> TheoremInfo | None:
        """Advance to next theorem with cheat."""
        while self.position < len(self.theorems) - 1:
            self.position += 1
            thm = self.current()
            if thm and thm.has_cheat and thm.name not in self.completed:
                return thm
        return None

    def goto(self, theorem_name: str) -> TheoremInfo | None:
        """Go to specific theorem by name."""
        for i, thm in enumerate(self.theorems):
            if thm.name == theorem_name:
                self.position = i
                return thm
        return None

    async def initialize(self) -> str:
        """Parse file, load HOL to first cheat, position cursor."""
        self._file_mtime = self.file.stat().st_mtime
        self.theorems = parse_file(self.file)

        if not self.theorems:
            return "No theorems found in file"

        if not self.session.is_running:
            await self.session.start()

        # Find first cheat
        first_cheat_idx = next(
            (i for i, t in enumerate(self.theorems) if t.has_cheat),
            None
        )

        if first_cheat_idx is None:
            return "No cheats found - all theorems already proved"

        thm = self.theorems[first_cheat_idx]

        # Get and load dependencies
        deps = await get_script_dependencies(self.file)
        for dep in deps:
            await self.session.send(f'load "{dep}";', timeout=60)

        # Load script content up to first cheat
        content = self.file.read_text()
        prefix = get_executable_content(content, thm.start_line)

        if prefix.strip():
            await self.session.send(prefix, timeout=300)

        self._loaded_to_line = thm.start_line
        self.position = first_cheat_idx
        return f"Positioned at {thm.name} (line {thm.start_line})"

    async def load_context_to(self, target_line: int) -> None:
        """Load file content from current loaded position to target line."""
        if target_line <= self._loaded_to_line:
            return  # Already loaded

        content = self.file.read_text()
        lines = content.split('\n')

        # Get content between loaded position and target
        # _loaded_to_line is 1-indexed, we want lines from _loaded_to_line to target_line-1
        additional = '\n'.join(lines[self._loaded_to_line:target_line - 1])

        if additional.strip():
            await self.session.send(additional, timeout=300)

        self._loaded_to_line = target_line

    async def start_current(self) -> str:
        """Set up goaltree for current theorem, replay tactics to cheat point."""
        thm = self.current()
        if not thm:
            return "ERROR: No current theorem"

        # Clear all proof state unconditionally
        await self.session.send('drop_all();', timeout=5)

        # Set up goal
        goal = thm.goal.replace('\n', ' ').strip()
        result = await self.session.send(f'gt `{goal}`;', timeout=30)

        if _is_hol_error(result):
            return f"ERROR setting up goal: {result[:500]}"

        # Get pre-cheat tactics using TacticParse (preserves >- structure)
        if thm.has_cheat and thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)
            extract_result = await self.session.send(
                f'extract_before_cheat "{escaped_body}";', timeout=30
            )
            # Parse SML string result: val it = "...": string
            before_cheat = _parse_sml_string(extract_result)
            if before_cheat:
                tac_result = await self.session.send(f'etq "{before_cheat}";', timeout=300)
                if _is_hol_error(tac_result):
                    return f"ERROR replaying tactics: {tac_result[:300]}"
                return f"Ready: {thm.name} (pre-cheat tactics replayed)"

        return f"Ready: {thm.name}"

    async def complete_and_advance(self) -> str:
        """Splice completed proof into file, advance to next cheat."""
        thm = self.current()
        if not thm:
            return "ERROR: No current theorem"

        # Get proof from p()
        p_output = await self.session.send("p();", timeout=30)
        tactic_script = parse_p_output(p_output)

        if not tactic_script:
            return f"ERROR: No proof found. Output:\n{p_output}"

        # Reject proofs with <anonymous> tactics (agent used e() instead of etq)
        if "<anonymous>" in tactic_script:
            return (
                "ERROR: Proof contains <anonymous> tactics. "
                "Use etq instead of e() to record tactic names."
            )

        # Check for external modifications before validation (more important error)
        if self._check_stale():
            return (
                f"ERROR: File modified since cursor initialized. "
                f"Proof for {thm.name} NOT saved. Reinitialize cursor to continue."
            )

        # Validate tactic syntax via TacticParse before splicing
        escaped = escape_sml_string(tactic_script)
        validate_result = await self.session.send(
            f'(TacticParse.parseTacticBlock "{escaped}"; "OK") handle _ => "PARSE_ERROR";',
            timeout=10
        )
        if "PARSE_ERROR" in validate_result or _is_hol_error(validate_result):
            return f"ERROR: Invalid tactic syntax, cannot splice:\n{tactic_script[:500]}"

        # Splice into file
        content = self.file.read_text()
        try:
            new_content = splice_into_theorem(content, thm.name, tactic_script)
        except ValueError:
            return f"ERROR: Failed to splice into {thm.name} (theorem not found)"
        atomic_write(self.file, new_content)
        self._file_mtime = self.file.stat().st_mtime  # Update after our write
        self.completed.add(thm.name)

        # Re-parse file (structure may have changed)
        self.theorems = parse_file(self.file)

        # Find and move to next cheat
        next_thm = self.next_cheat()

        if next_thm:
            return f"Completed {thm.name}, next: {next_thm.name} (line {next_thm.start_line})"
        else:
            return f"Completed {thm.name} - no more cheats!"

    @property
    def status(self) -> dict:
        """Get cursor status."""
        current = self.current()
        cheats = [
            {"name": t.name, "line": t.start_line}
            for t in self.theorems
            if t.has_cheat and t.name not in self.completed
        ]
        return {
            "file": str(self.file),
            "current": current.name if current else None,
            "current_line": current.start_line if current else None,
            "position": f"{self.position + 1}/{len(self.theorems)}",
            "completed": list(self.completed),
            "cheats": cheats,
        }
