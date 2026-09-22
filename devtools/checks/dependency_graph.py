"""AST/file helpers for the canonical compiler architecture audit."""

from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path

from devtools.paths import repository_root

ROOT = repository_root()
SRC = ROOT / "src" / "number_compiler"


@dataclass(frozen=True, slots=True)
class SourceSyntax:
    """Syntactic facts for audits that must ignore comments and string data."""

    identifiers: frozenset[str]
    imports: frozenset[str]
    functions: frozenset[str]
    classes: frozenset[str]
    exports: frozenset[str]
    export_modules: frozenset[str]
    dynamic_imports: frozenset[str]
    unknown_dynamic_import: bool


def source_syntax(path: Path) -> SourceSyntax:
    """Index executable Python syntax without importing the target module."""
    tree = _tree(path)
    export_tables = {"__all__", "_EXPORT_MODULES"}
    identifiers: set[str] = set()
    imports: set[str] = set()
    functions: set[str] = set()
    classes: set[str] = set()
    exports: set[str] = set()
    export_modules: set[str] = set()
    dynamic_imports: set[str] = set()
    unknown_dynamic_import = False
    dynamic_loaders = {"__import__", "import_module"}
    for declaration in ast.walk(tree):
        if isinstance(declaration, ast.ImportFrom) and declaration.module in {
            "importlib",
            "builtins",
        }:
            dynamic_loaders.update(
                alias.asname or alias.name
                for alias in declaration.names
                if alias.name in {"__import__", "import_module"}
            )
    for statement in tree.body:
        if not isinstance(statement, ast.Assign):
            continue
        assigned = {
            target.id for target in statement.targets if isinstance(target, ast.Name)
        }
        if not assigned.intersection(export_tables):
            continue
        try:
            literal = ast.literal_eval(statement.value)
        except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
            # Nonliteral export tables require a separate dynamic audit.
            raise ValueError(f"nonliteral package export table: {path}") from None
        if "__all__" in assigned:
            if not isinstance(literal, (list, tuple)) or any(
                type(item) is not str for item in literal
            ):
                raise ValueError(f"invalid __all__ export table: {path}")
            exports.update(literal)
        if "_EXPORT_MODULES" in assigned:
            if type(literal) is not dict or any(
                type(key) is not str or type(value) is not str
                for key, value in literal.items()
            ):
                raise ValueError(f"invalid lazy export table: {path}")
            exports.update(literal)
            export_modules.update(literal.values())
    for node in ast.walk(tree):
        if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
            if node.target.id in export_tables:
                raise ValueError(f"dynamic package export table: {path}")
        if isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Name)
            and target.value.id in export_tables
            for target in node.targets
        ):
            raise ValueError(f"dynamic package export table: {path}")
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
            identifiers.update(
                alias.asname or alias.name.split(".")[0] for alias in node.names
            )
        elif isinstance(node, ast.ImportFrom):
            base = "." * node.level + (node.module or "")
            imports.add(base)
            imports.update(
                base + ("." if node.module else "") + alias.name
                for alias in node.names
                if alias.name != "*"
            )
            identifiers.update(alias.name for alias in node.names)
            identifiers.update(alias.asname or alias.name for alias in node.names)
        elif isinstance(node, ast.Name):
            identifiers.add(node.id)
        elif isinstance(node, ast.Attribute):
            identifiers.add(node.attr)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions.add(node.name)
            identifiers.add(node.name)
        elif isinstance(node, ast.ClassDef):
            classes.add(node.name)
            identifiers.add(node.name)
        elif isinstance(node, ast.Call):
            target = node.func
            if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name):
                if target.value.id in export_tables:
                    raise ValueError(f"dynamic package export table: {path}")
            if (
                isinstance(target, ast.Name)
                and target.id in dynamic_loaders
                or isinstance(target, ast.Attribute)
                and target.attr == "import_module"
            ):
                if (
                    node.args
                    and isinstance(node.args[0], ast.Constant)
                    and type(node.args[0].value) is str
                ):
                    dynamic_imports.add(node.args[0].value)
                else:
                    unknown_dynamic_import = True
    return SourceSyntax(
        frozenset(identifiers),
        frozenset(imports),
        frozenset(functions),
        frozenset(classes),
        frozenset(exports),
        frozenset(export_modules),
        frozenset(dynamic_imports),
        unknown_dynamic_import,
    )


def _tree(path: Path) -> ast.Module:
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
