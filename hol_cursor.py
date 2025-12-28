"""Proof cursor for navigating through theorems without reloading."""

import asyncio
import os
import re
import tempfile
from pathlib import Path

from hol_file_parser import TheoremInfo, parse_file, splice_into_theorem, parse_p_output
from hol_session import HOLSession, HOLDIR


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
    """Extract executable SML content from script, skipping Theory/Ancestors header.

    For script format files, skips the Theory/Ancestors declarations.
    Returns content from line 1 to up_to_line-1.
    """
    lines = content.split('\n')
    prefix_lines = lines[:up_to_line - 1]

    # Check for script format and find where executable content starts
    in_header = False
    start_idx = 0

    for i, line in enumerate(prefix_lines):
        stripped = line.strip()
        if stripped.startswith('Theory '):
            in_header = True
        elif in_header and stripped and not stripped[0].isspace() and not stripped.startswith('Ancestors'):
            # First non-indented, non-Ancestors line after Theory = end of header
            # But check if it's still part of Ancestors (multi-line)
            if not re.match(r'^\s*\w+(\s+\w+)*\s*$', stripped):
                start_idx = i
                break
        elif in_header and stripped.startswith('(*'):
            # Comment after header = start of executable content
            start_idx = i
            break

    return '\n'.join(prefix_lines[start_idx:])


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

        self.position = first_cheat_idx
        return f"Positioned at {thm.name} (line {thm.start_line})"

    async def start_current(self) -> str:
        """Set up goaltree for current theorem, replay tactics to cheat point."""
        thm = self.current()
        if not thm:
            return "ERROR: No current theorem"

        # Clear any existing goaltree first
        await self.session.send('drop();', timeout=5)

        # Set up goal
        goal = thm.goal.replace('\n', ' ').strip()
        result = await self.session.send(f'gt `{goal}`;', timeout=30)

        if 'Exception' in result or 'error' in result.lower():
            return f"ERROR setting up goal: {result[:500]}"

        # Replay tactics before cheat
        for tac in thm.tactics_before_cheat:
            tac_result = await self.session.send(f'etq "{tac}";', timeout=60)
            if 'Exception' in tac_result:
                return f"ERROR replaying tactic '{tac}': {tac_result[:300]}"

        replayed = len(thm.tactics_before_cheat)
        return f"Ready: {thm.name} ({replayed} tactics replayed)"

    async def complete_and_advance(self) -> str:
        """Splice completed proof into file, advance to next cheat."""
        thm = self.current()
        if not thm:
            return "ERROR: No current theorem"

        # Get proof from p()
        p_output = await self.session.send("p();", timeout=30)
        tactic_script = parse_p_output(p_output)

        if not tactic_script:
            return f"ERROR: No proof found. Output:\n{p_output[:500]}"

        # Splice into file
        content = self.file.read_text()
        try:
            new_content = splice_into_theorem(content, thm.name, tactic_script)
        except ValueError:
            return f"ERROR: Failed to splice into {thm.name} (file modified externally?)"
        atomic_write(self.file, new_content)
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
