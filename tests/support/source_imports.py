"""Content-validated immutable import facts shared by structural checks.

Each caller still reads the file. Only unchanged parse results are reused;
neither mutable ASTs nor warmed execution arenas cross test boundaries.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path


@dataclass(frozen=True, slots=True)
class ImportAlias:
    name: str
    asname: str | None


@dataclass(frozen=True, slots=True)
class Import:
    names: tuple[ImportAlias, ...]


@dataclass(frozen=True, slots=True)
class ImportFrom:
    module: str | None
    level: int
    names: tuple[ImportAlias, ...]


ImportFact = Import | ImportFrom
_facts: dict[Path, tuple[bytes, tuple[ImportFact, ...]]] = {}


def source_imports(path: Path) -> tuple[Import | ImportFrom, ...]:
    """Return all imports, including nested imports, without retaining an AST."""
    source = path.read_bytes()
    digest = sha256(source).digest()
    previous = _facts.get(path)
    if previous is not None and previous[0] == digest:
        return previous[1]
    facts: list[ImportFact] = []
    for node in ast.walk(ast.parse(source, filename=str(path))):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            aliases = tuple(
                ImportAlias(alias.name, alias.asname) for alias in node.names
            )
            facts.append(
                ImportFrom(node.module, node.level, aliases)
                if isinstance(node, ast.ImportFrom)
                else Import(aliases)
            )
    result = tuple(facts)
    _facts[path] = digest, result
    return result
