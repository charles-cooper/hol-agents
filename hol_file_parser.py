"""Parse HOL4 script files for theorem structure."""

import re
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class TheoremInfo:
    """Information about a theorem in a HOL script file."""
    name: str
    kind: str  # "Theorem" or "Triviality"
    goal: str  # The statement to prove
    start_line: int  # Line of "Theorem name:"
    proof_start_line: int  # Line of "Proof"
    proof_end_line: int  # Line of "QED"
    has_cheat: bool
    tactics_before_cheat: list[str] = field(default_factory=list)
    attributes: list[str] = field(default_factory=list)


def parse_theorems(content: str) -> list[TheoremInfo]:
    """Parse .sml file content, return all theorems in order."""
    theorems = []
    lines = content.split('\n')

    # Pattern for Theorem/Triviality with optional attributes
    # Matches: Theorem name:, Theorem name[simp]:, Triviality foo[local,simp]:
    header_pattern = re.compile(
        r'^(Theorem|Triviality)\s+(\w+)(?:\s*\[([^\]]*)\])?\s*:',
        re.MULTILINE
    )

    for match in header_pattern.finditer(content):
        kind = match.group(1)
        name = match.group(2)
        attrs_str = match.group(3)
        attributes = [a.strip() for a in attrs_str.split(',')] if attrs_str else []

        # Find line number of header
        start_pos = match.start()
        start_line = content[:start_pos].count('\n') + 1

        # Find Proof and QED after this point
        rest = content[match.end():]

        proof_match = re.search(r'^\s*Proof\s*$', rest, re.MULTILINE)
        if not proof_match:
            continue

        qed_match = re.search(r'^\s*QED\s*$', rest, re.MULTILINE)
        if not qed_match:
            continue

        # Extract goal (between : and Proof)
        goal = rest[:proof_match.start()].strip()

        # Calculate line numbers
        proof_start_line = start_line + rest[:proof_match.start()].count('\n') + 1
        proof_end_line = start_line + rest[:qed_match.start()].count('\n') + 1

        # Extract proof body
        proof_body = rest[proof_match.end():qed_match.start()]

        # Check for cheat
        has_cheat = bool(re.search(r'\bcheat\b', proof_body, re.IGNORECASE))

        # Parse tactics before cheat
        tactics_before_cheat = []
        if has_cheat:
            tactics_before_cheat = _parse_tactics_before_cheat(proof_body)

        theorems.append(TheoremInfo(
            name=name,
            kind=kind,
            goal=goal,
            start_line=start_line,
            proof_start_line=proof_start_line,
            proof_end_line=proof_end_line,
            has_cheat=has_cheat,
            tactics_before_cheat=tactics_before_cheat,
            attributes=attributes,
        ))

    return theorems


def _parse_tactics_before_cheat(proof_body: str) -> list[str]:
    """Extract tactics before cheat, splitting on \\\\ at top level."""
    # Find content before 'cheat'
    cheat_match = re.search(r'\bcheat\b', proof_body, re.IGNORECASE)
    if not cheat_match:
        return []

    before_cheat = proof_body[:cheat_match.start()]

    # Split on \\ at top level (not inside parentheses)
    tactics = []
    current = ""
    paren_depth = 0
    i = 0

    while i < len(before_cheat):
        char = before_cheat[i]

        if char == '(':
            paren_depth += 1
            current += char
        elif char == ')':
            paren_depth -= 1
            current += char
        elif char == '\\' and i + 1 < len(before_cheat) and before_cheat[i + 1] == '\\':
            if paren_depth == 0:
                tac = current.strip()
                if tac:
                    tactics.append(tac)
                current = ""
                i += 1  # Skip second backslash
            else:
                current += char
        elif char == '>' and i + 1 < len(before_cheat) and before_cheat[i + 1] == '-':
            # >- is a subgoal combinator, treat like \\
            if paren_depth == 0:
                tac = current.strip()
                if tac:
                    tactics.append(tac)
                current = ""
                i += 1  # Skip the -
            else:
                current += char
        else:
            current += char

        i += 1

    # Don't add final segment - it leads to cheat
    return tactics

def parse_file(path: Path) -> list[TheoremInfo]:
    """Parse .sml file, return all theorems."""
    content = path.read_text()
    return parse_theorems(content)


def splice_into_theorem(content: str, name: str, tactics: str) -> str:
    """Replace Proof...QED block for named theorem with new tactics.

    Raises:
        ValueError: If theorem not found in content.
    """
    # Match Theorem/Triviality name[...]: ... Proof ... QED
    pattern = rf'''
        ((?:Theorem|Triviality)\s+{re.escape(name)}
         (?:\s*\[[^\]]*\])?    # optional attributes
         \s*:\s*
         .*?                   # goal (non-greedy)
         \n\s*Proof\s*\n)      # Proof line
        (.*?)                  # old tactics
        (\n\s*QED)             # QED line
    '''

    def replacer(m):
        header = m.group(1)
        footer = m.group(3)
        indented = _indent(tactics, "  ")
        return f"{header}{indented}{footer}"

    new_content = re.sub(pattern, replacer, content, flags=re.DOTALL | re.VERBOSE)
    if new_content == content:
        raise ValueError(f"Theorem '{name}' not found")
    return new_content


def _indent(text: str, prefix: str) -> str:
    """Indent non-empty lines."""
    return '\n'.join(
        prefix + line if line.strip() else line
        for line in text.split('\n')
    )


def parse_p_output(output: str) -> str | None:
    """Extract tactic script from p() output.

    p() output looks like:
    > p();
    tac1 \\ tac2 >- (...) ...
    val it = () : unit

    Returns None if output contains errors or no valid tactic script.
    """
    # Reject error output before parsing
    if 'Exception' in output or 'HOL_ERR' in output or 'No goalstack' in output:
        return None

    lines = output.split('\n')
    tactic_lines = []

    for line in lines:
        stripped = line.strip()
        # Skip command echo and prompts
        if stripped.startswith('>') or stripped == 'p();':
            continue
        # Stop at val binding
        if stripped.startswith('val '):
            break
        # Skip "OK" markers from goaltree
        if stripped == 'OK':
            continue
        # Collect tactic content
        if stripped:
            tactic_lines.append(line.rstrip())

    return '\n'.join(tactic_lines).strip() or None
