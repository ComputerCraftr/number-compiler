"""Conservative source lexer for the Isabelle syntax used by proof inventory.

This is a navigation parser, not an Isabelle AST or a substitute for a build.
Unsupported source layout raises ValueError instead of inventing dependencies.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Session:
    name: str
    directory: Path
    parent: str
    dependencies: tuple[str, ...]
    theories: tuple[str, ...]


@dataclass(frozen=True)
class RootOption:
    """One key/value item in a ROOT ``options [...]`` block."""

    line: int
    name: str
    value: str


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


_DOCUMENT_START = re.compile(r"(?m)^[ \t]*text(?:_raw)?\s+\\<open>")
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


def global_simp_registrations(text: str, fact: str) -> tuple[int, ...]:
    """Locate authored declare/lemmas registrations of a specified fact.

    This is a lexical policy check, not a theorem dependency analysis. Local
    ``simp add:`` use remains allowed. Reuse the navigation masks so comments,
    documentation, ML and quoted propositions cannot masquerade as commands.
    """
    clean = navigation_text(text)
    name = r"[A-Za-z_][A-Za-z0-9_'.]*"
    commands = unquoted_matches(re.compile(r"(?m)^[ \t]*(declare|lemmas)\b"), clean)

    def adds_simp(attributes: str) -> bool:
        return any(
            re.match(r"\s*simp(?:\s|$)", attribute)
            and not re.match(r"\s*simp\s+del\b", attribute)
            for attribute in attributes.split(",")
        )

    def matches(reference: str) -> bool:
        return reference == fact or reference.endswith("." + fact)

    lines: list[int] = []
    for command in commands:
        rest = clean[command.end() :]
        if command.group(1) == "declare":
            # Each declaration item has its own attributes. Stop when the next
            # token is not such an item, rather than consuming another command.
            offset = 0
            while item := re.match(rf"\s*({name})\s*\[([^\]]*)\]", rest[offset:]):
                if matches(item.group(1)) and adds_simp(item.group(2)):
                    lines.append(clean.count("\n", 0, command.start()) + 1)
                offset += item.end()
        else:
            alias = re.match(rf"\s*{name}\s*\[([^\]]*)\]\s*=\s*({name})\b", rest)
            if alias and adds_simp(alias.group(1)) and matches(alias.group(2)):
                lines.append(clean.count("\n", 0, command.start()) + 1)
            reference = re.match(
                rf"\s*{name}\s*(?:\[[^\]]*\])?\s*=\s*({name})\s*\[([^\]]*)\]",
                rest,
            )
            if (
                reference
                and matches(reference.group(1))
                and adds_simp(reference.group(2))
            ):
                lines.append(clean.count("\n", 0, command.start()) + 1)
    return tuple(dict.fromkeys(lines))


_SESSION = re.compile(
    r'(?m)^session\s+(\w+)(?:\s+in\s+("[^"]+"|[^\s=]+))?\s*='
    r'\s+("[^"]+"|[^\s+]+)\s*\+'
)
_ROOT_OPTIONS = re.compile(r"\boptions\s*\[")
_DEPENDENCIES = re.compile(r"(?ms)^[ \t]{2}sessions\s+(.*?)(?=^[ \t]{2}\w|\Z)")
_THEORIES = re.compile(r"(?ms)^[ \t]{2}theories\s+(.*?)(?=^[ \t]{2}\w|\Z)")
_THEORY = re.compile(r"(?m)^\s*theory\s+([A-Za-z][A-Za-z0-9_]*)\s+imports\s+")
_TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[A-Za-z0-9_./-]+')


_ML_START = re.compile(r"(?m)^[ \t]*ML(?:_val|_prf)?\s+\\<open>")
_DYNAMIC_CARTOUCHE_START = re.compile(
    r"(?m)^[ \t]*(?:ML(?:_val|_prf)?|local_setup|setup)\s+\\<open>"
)


def _cartouche_spans(
    text: str, pattern: re.Pattern[str]
) -> tuple[tuple[int, int, str], ...]:
    starts = unquoted_matches(pattern, text)
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
            raise ValueError("unterminated Isabelle dynamic cartouche")
        blocks.append((match.start(), offset, text[match.end() : offset - len(_CLOSE)]))
        previous_end = offset
    return tuple(blocks)


def ml_cartouche_spans(text: str) -> tuple[tuple[int, int, str], ...]:
    """Locate top-level ML commands without accepting quoted fake commands."""
    return _cartouche_spans(text, _ML_START)


def dynamic_cartouche_spans(text: str) -> tuple[tuple[int, int, str], ...]:
    """Locate ML/setup cartouches whose contents are dynamically interpreted."""
    return _cartouche_spans(text, _DYNAMIC_CARTOUCHE_START)


def ml_cartouches(text: str) -> tuple[str, ...]:
    return tuple(body for _, _, body in ml_cartouche_spans(text))


def navigation_text(text: str) -> str:
    """Keep theorem statements, but mask ML command bodies for declarations."""
    clean = executable_text(text)
    output = list(clean)
    for start, end, _ in dynamic_cartouche_spans(clean):
        for position in range(start, end):
            if output[position] != "\n":
                output[position] = " "
    return "".join(output)


def unquoted_numeric_case_facts(text: str) -> tuple[int, ...]:
    """Reject generated case names whose dot otherwise ends an Isar proof."""
    clean = navigation_text(text)
    pattern = re.compile(r"(?<![\w.])\d+\.(?:prems|hyps|IH)\b")
    return tuple(
        clean.count("\n", 0, match.start()) + 1
        for match in unquoted_matches(pattern, clean)
    )


def _theory_entries(block: str, session: str) -> tuple[str, ...]:
    """Keep every ROOT theory entry, or reject syntax we cannot interpret."""
    entries: list[str] = []
    cursor = 0
    for token in _TOKEN.finditer(block):
        value = token.group(0)
        quoted = value.startswith('"')
        if block[cursor : token.start()].strip() or (
            not quoted and re.fullmatch(r"[A-Za-z0-9_]+", value) is None
        ):
            raise ValueError(f"{session}: unsupported ROOT theory entry")
        name = value[1:-1] if quoted else value
        if not name or "\\" in name:
            raise ValueError(f"{session}: unsupported ROOT theory entry")
        entries.append(name)
        cursor = token.end()
    if block[cursor:].strip():
        raise ValueError(f"{session}: unsupported ROOT theory entry")
    return tuple(entries)


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
            _theory_entries(theory_match.group(1), match.group(1))
            if theory_match
            else ()
        )
        raw_directory = match.group(2)
        if (
            raw_directory
            and not raw_directory.startswith('"')
            and re.fullmatch(r"[A-Za-z0-9_]+", raw_directory) is None
        ):
            raise ValueError(f"{match.group(1)}: ROOT session path requires quotes")
        directory = Path(raw_directory.strip('"') if raw_directory else ".")
        if directory.is_absolute() or ".." in directory.parts:
            raise ValueError(f"{match.group(1)}: session directory escapes theory root")
        sessions.append(
            Session(
                match.group(1),
                directory,
                match.group(3).strip('"'),
                _theory_entries(dependency_match.group(1), match.group(1))
                if dependency_match
                else (),
                theories,
            )
        )
    validate_sessions(tuple(sessions))
    return tuple(sessions)


def validate_sessions(sessions: tuple[Session, ...]) -> None:
    """Check uniqueness and ancestry across all registered ROOT files."""
    if len({session.name for session in sessions}) != len(sessions):
        raise ValueError("duplicate Isabelle session declaration")
    if len({session.directory for session in sessions}) != len(sessions):
        raise ValueError("duplicate Isabelle session directory")
    # External parents are supplied by the Isabelle installation. Only local
    # ancestry can be checked here; neither parent nor session edges may cycle.
    local = {session.name: session for session in sessions}
    completed: set[str] = set()
    visiting: set[str] = set()
    for name in local:
        pending = [(name, False)]
        while pending:
            current, returning = pending.pop()
            if returning:
                visiting.remove(current)
                completed.add(current)
            elif current in local and current not in completed:
                if current in visiting:
                    raise ValueError(f"cyclic Isabelle session dependency: {current}")
                visiting.add(current)
                pending.append((current, True))
                session = local[current]
                pending.extend(
                    (dependency, False)
                    for dependency in (session.parent, *session.dependencies)
                )


def root_option_assignments(text: str) -> tuple[RootOption, ...]:
    """Read assignments in ROOT options blocks, ignoring comments and strings.

    This intentionally handles only the lexical shape needed by policy checks;
    it does not attempt to validate Isabelle option names or their types.
    """
    clean = mask_comments(text)
    assignments: list[RootOption] = []
    for match in unquoted_matches(_ROOT_OPTIONS, clean):
        start = match.end()
        offset = start
        depth = 1
        quoted = False
        while offset < len(clean) and depth:
            char = clean[offset]
            if quoted and char == "\\":
                offset += 2
                continue
            if char == '"':
                quoted = not quoted
            elif not quoted and char == "[":
                depth += 1
            elif not quoted and char == "]":
                depth -= 1
                if depth == 0:
                    break
            offset += 1
        if depth:
            raise ValueError("unterminated ROOT options block")

        content = clean[start:offset]
        item_start = 0
        quoted = False
        item_offset = 0
        items: list[tuple[int, str]] = []
        while item_offset < len(content):
            char = content[item_offset]
            if quoted and char == "\\":
                item_offset += 2
                continue
            if char == '"':
                quoted = not quoted
            elif char == "," and not quoted:
                items.append((item_start, content[item_start:item_offset]))
                item_start = item_offset + 1
            item_offset += 1
        items.append((item_start, content[item_start:]))
        for item_start, item in items:
            name, separator, value = item.partition("=")
            if separator and name.strip():
                leading = len(item) - len(item.lstrip())
                line = clean.count("\n", 0, start + item_start) + 1
                line += item[:leading].count("\n")
                assignments.append(RootOption(line, name.strip(), value.strip()))
    return tuple(assignments)


def session_dependency_closure(
    sessions: tuple[Session, ...], selected: Iterable[str]
) -> tuple[str, ...]:
    """Return selected local sessions and their ROOT-declared dependencies.

    Isabelle installation parents such as ``HOL`` are absent from ``sessions``
    and therefore do not count as project sessions.  The result follows ROOT
    declaration order, which keeps selection manifests deterministic.
    """
    by_name = {session.name: session for session in sessions}
    requested = tuple(dict.fromkeys(selected))
    missing = tuple(name for name in requested if name not in by_name)
    if missing:
        raise ValueError(f"unknown Isabelle session selection: {', '.join(missing)}")

    reached: set[str] = set()
    pending = list(requested)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        session = by_name[name]
        pending.extend(
            dependency
            for dependency in (session.parent, *session.dependencies)
            if dependency in by_name and dependency not in reached
        )
    return tuple(session.name for session in sessions if session.name in reached)


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
        quoted = value.startswith('"')
        if clean[cursor : token.start()].strip():
            raise ValueError(f"{path}: unsupported theory/imports header")
        if value == "begin":
            break
        if not quoted and "-" in value:
            raise ValueError(f"{path}: unquoted symbolic token in theory import")
        imports.append(value[1:-1] if quoted else value)
        cursor = token.end()
    else:
        raise ValueError(f"{path}: missing theory begin")
    if not imports:
        raise ValueError(f"{path}: missing theory imports")
    return match.group(1), tuple(imports)
