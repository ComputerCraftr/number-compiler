"""AST/file helpers for the canonical compiler architecture audit."""

from __future__ import annotations

import ast
from pathlib import Path

from devtools.paths import repository_root

ROOT = repository_root()
SRC = ROOT / "src" / "number_compiler"


def _tree(path: Path) -> ast.AST:
    return ast.parse(path.read_text(), filename=str(path))


def _module_path(name: str) -> Path:
    """Resolve a qualified package-local module, including package initializers."""
    candidate = SRC.joinpath(*name.split("."))
    return (
        candidate / "__init__.py"
        if candidate.is_dir()
        else candidate.with_suffix(".py")
    )


def _package_imports(path: Path) -> set[str]:
    """Qualified runtime imports, preserving subpackages and module aliases."""
    relative = path.relative_to(SRC).with_suffix("").parts
    package = ("number_compiler", *relative[:-1])
    out: set[str] = set()
    pending = list(ast.iter_child_nodes(_tree(path)))
    while pending:
        node = pending.pop()
        if isinstance(node, ast.If) and (
            isinstance(node.test, ast.Name)
            and node.test.id == "TYPE_CHECKING"
            or isinstance(node.test, ast.Attribute)
            and node.test.attr == "TYPE_CHECKING"
        ):
            pending.extend(node.orelse)
            continue
        pending.extend(ast.iter_child_nodes(node))
        candidates: list[str] = []
        if isinstance(node, ast.ImportFrom):
            base = (
                ".".join(package[: len(package) - node.level + 1])
                + ("." + node.module if node.module else "")
                if node.level
                else node.module or ""
            )
            candidates.append(base)
            candidates.extend(base + "." + alias.name for alias in node.names)
        elif isinstance(node, ast.Import):
            candidates.extend(alias.name for alias in node.names)
        for imported in candidates:
            if imported.startswith("number_compiler."):
                local = imported.removeprefix("number_compiler.")
                if _module_path(local).is_file():
                    out.add(local)
    return out


def _reachable(start: str) -> set[str]:
    """Follow runtime dependencies through regular subpackages."""
    todo, seen = [start], set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        path = _module_path(name)
        if not path.is_file():
            continue
        seen.add(name)
        todo.extend(sorted(_package_imports(path) - seen))
    return seen
