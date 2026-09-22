"""Conservative source lexer for the Isabelle syntax used by proof inventory.

This is a navigation parser, not an Isabelle AST or a substitute for a build.
Unsupported source layout raises ValueError instead of inventing dependencies.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Session:
    name: str
    directory: Path
    parent: str
    dependencies: tuple[str, ...]
    theories: tuple[str, ...]


def mask_comments(text: str) -> str:
    """Erase nested Isabelle comments, preserving character and line offsets."""
    output: list[str] = []
    depth = 0
    quoted = False
    offset = 0
    while offset < len(text):
        pair = text[offset : offset + 2]
        if depth == 0 and text[offset] == '"':
            quoted = not quoted
            output.append('"')
            offset += 1
        elif depth == 0 and quoted and pair.startswith("\\"):
            output.append(pair)
            offset += len(pair)
        elif not quoted and pair == "(*":
            depth += 1
            output.append("  ")
            offset += 2
        elif depth and pair == "*)":
            depth -= 1
            output.append("  ")
            offset += 2
        else:
            char = text[offset]
            output.append(char if depth == 0 or char == "\n" else " ")
            offset += 1
    if depth:
        raise ValueError("unterminated Isabelle comment")
    return "".join(output)


_DOCUMENT_START = re.compile(r"(?m)^text(?:_raw)?\s+\\<open>")
_OPEN = "\\<open>"
_CLOSE = "\\<close>"


def unquoted_matches(pattern: re.Pattern[str], text: str) -> tuple[re.Match[str], ...]:
    """Find command candidates whose first character is outside a quoted string."""
    found: list[re.Match[str]] = []
    offset = 0
    quoted = False
    for match in pattern.finditer(text):
        while offset < match.start():
            if quoted and text[offset] == "\\":
                offset += 2
            elif text[offset] == '"':
                quoted = not quoted
                offset += 1
            else:
                offset += 1
        if not quoted:
            found.append(match)
    return tuple(found)


def documentation_spans(text: str) -> tuple[tuple[int, int, str], ...]:
    """Locate top-level documentation in comment-free Isabelle text."""
    spans: list[tuple[int, int, str]] = []
    previous_end = 0
    for match in unquoted_matches(_DOCUMENT_START, text):
        if match.start() < previous_end:
            continue
        offset = match.end()
        depth = 1
        while offset < len(text) and depth:
            if text.startswith(_OPEN, offset):
                depth += 1
                offset += len(_OPEN)
            elif text.startswith(_CLOSE, offset):
                depth -= 1
                offset += len(_CLOSE)
            else:
                offset += 1
        if depth:
            raise ValueError("unterminated Isabelle documentation cartouche")
        spans.append((match.start(), offset, text[match.end() : offset - len(_CLOSE)]))
        previous_end = offset
    return tuple(spans)


def first_documentation_scope(text: str) -> str:
    spans = documentation_spans(mask_comments(text))
    return " ".join(spans[0][2].split()) if spans else ""


def executable_text(text: str) -> str:
    """Erase comments and nested documentation cartouches, retaining line numbers."""
    clean = mask_comments(text)
    output = list(clean)
    for start, end, _ in documentation_spans(clean):
        for position in range(start, end):
            if output[position] != "\n":
                output[position] = " "
    return "".join(output)


_SESSION = re.compile(
    r'(?m)^session\s+(\w+)(?:\s+in\s+("[^"]+"|[^\s=]+))?\s*='
    r'\s+("[^"]+"|[^\s+]+)\s*\+'
)
_DEPENDENCIES = re.compile(r"(?m)^\s{2}sessions\s+(.+)$")
_THEORIES = re.compile(r"(?ms)^\s{2}theories\s*\n(.*?)(?=^\s{2}\w|\Z)")
_THEORY = re.compile(r"(?m)^\s*theory\s+([A-Za-z][A-Za-z0-9_]*)\s+imports\s+")
_TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[A-Za-z0-9_./-]+')


_ML_START = re.compile(r"(?m)^ML(?:_val)?\s+\\<open>")


def ml_cartouche_spans(text: str) -> tuple[tuple[int, int, str], ...]:
    """Locate top-level ML commands without accepting quoted fake commands."""
    starts = unquoted_matches(_ML_START, text)
    blocks: list[tuple[int, int, str]] = []
    previous_end = 0
    for match in starts:
        if match.start() < previous_end:
            continue
        offset = match.end()
        depth = 1
        quoted = False
        while offset < len(text) and depth:
            if quoted and text[offset] == "\\":
                offset += 2
            elif text[offset] == '"':
                quoted = not quoted
                offset += 1
            elif not quoted and text.startswith(_OPEN, offset):
                depth += 1
                offset += len(_OPEN)
            elif not quoted and text.startswith(_CLOSE, offset):
                depth -= 1
                offset += len(_CLOSE)
            else:
                offset += 1
        if depth:
            raise ValueError("unterminated Isabelle ML cartouche")
        blocks.append((match.start(), offset, text[match.end() : offset - len(_CLOSE)]))
        previous_end = offset
    return tuple(blocks)


def ml_cartouches(text: str) -> tuple[str, ...]:
    return tuple(body for _, _, body in ml_cartouche_spans(text))


def navigation_text(text: str) -> str:
    """Keep theorem statements, but mask ML command bodies for declarations."""
    clean = executable_text(text)
    output = list(clean)
    for start, end, _ in ml_cartouche_spans(clean):
        for position in range(start, end):
            if output[position] != "\n":
                output[position] = " "
    return "".join(output)


def parse_sessions(text: str) -> tuple[Session, ...]:
    clean = mask_comments(text)
    starts = unquoted_matches(_SESSION, clean)
    declared_lines = unquoted_matches(re.compile(r"(?m)^session\b"), clean)
    if len(declared_lines) != len(starts):
        raise ValueError("ROOT contains an unsupported session declaration")
    if clean.strip() and not starts:
        raise ValueError("ROOT has no supported session declarations")
    sessions: list[Session] = []
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(clean)
        body = clean[match.end() : end]
        dependencies = unquoted_matches(_DEPENDENCIES, body)
        theory_blocks = unquoted_matches(_THEORIES, body)
        if len(dependencies) > 1 or len(theory_blocks) > 1:
            raise ValueError(f"{match.group(1)}: repeated ROOT section")
        dependency_match = dependencies[0] if dependencies else None
        theory_match = theory_blocks[0] if theory_blocks else None
        theories = (
            tuple(re.findall(r"(?m)^\s{4}([A-Za-z0-9_]+)\s*$", theory_match.group(1)))
            if theory_match
            else ()
        )
        directory = Path(match.group(2).strip('"') if match.group(2) else ".")
        if directory.is_absolute() or ".." in directory.parts:
            raise ValueError(f"{match.group(1)}: session directory escapes theory root")
        sessions.append(
            Session(
                match.group(1),
                directory,
                match.group(3).strip('"'),
                tuple(dependency_match.group(1).split()) if dependency_match else (),
                theories,
            )
        )
    if len({session.name for session in sessions}) != len(sessions):
        raise ValueError("duplicate Isabelle session declaration")
    return tuple(sessions)


def parse_theory_header(text: str, path: Path) -> tuple[str, tuple[str, ...]]:
    clean = executable_text(text)
    candidates = unquoted_matches(_THEORY, clean)
    if not candidates:
        raise ValueError(f"{path}: missing theory/imports header")
    match = candidates[0]
    tokens = _TOKEN.finditer(clean, match.end())
    imports: list[str] = []
    cursor = match.end()
    for token in tokens:
        value = token.group(0)
        if clean[cursor : token.start()].strip():
            raise ValueError(f"{path}: unsupported theory/imports header")
        if value == "begin":
            break
        imports.append(value.strip('"'))
        cursor = token.end()
    else:
        raise ValueError(f"{path}: missing theory begin")
    if not imports:
        raise ValueError(f"{path}: missing theory imports")
    return match.group(1), tuple(imports)
