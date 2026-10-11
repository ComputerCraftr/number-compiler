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
    dynamic_import_routes: frozenset[tuple[str, str | None]]
    import_references: tuple[tuple[int, str], ...]


def source_syntax(
    path: Path,
    *,
    tree: ast.Module | None = None,
    source_root: Path | None = None,
) -> SourceSyntax:
    """Index executable Python syntax without importing the target module."""
    path = Path(path).resolve()
    source_root = Path(SRC if source_root is None else source_root).resolve()
    tree = tree if tree is not None else _tree(path)
    try:
        package: tuple[str, ...] | None = module_package(path, source_root)
    except ValueError:
        package = None
    export_tables = {"__all__", "_EXPORT_MODULES"}
    identifiers: set[str] = set()
    imports: set[str] = set()
    functions: set[str] = set()
    classes: set[str] = set()
    exports: set[str] = set()
    export_modules: set[str] = set()
    dynamic_imports: set[str] = set()
    dynamic_import_routes: set[tuple[str, str | None]] = set()
    import_refs: list[tuple[int, str]] = []
    imported_loaders: list[ast.ImportFrom] = []
    dynamic_calls: list[ast.Call] = []
    unknown_dynamic_import = False
    dynamic_loaders = {"__import__", "import_module"}
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
        if (
            isinstance(node, ast.AugAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id in export_tables
        ):
            raise ValueError(f"dynamic package export table: {path}")
        if isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Name)
            and target.value.id in export_tables
            for target in node.targets
        ):
            raise ValueError(f"dynamic package export table: {path}")
        if isinstance(node, ast.Import):
            import_refs.extend((node.lineno, alias.name) for alias in node.names)
            imports.update(alias.name for alias in node.names)
            identifiers.update(
                alias.asname or alias.name.split(".")[0] for alias in node.names
            )
        elif isinstance(node, ast.ImportFrom):
            import_refs.extend(
                (node.lineno, imported)
                for imported in _resolved_import_from_names(node, package)
            )
            base = "." * node.level + (node.module or "")
            imports.add(base)
            imports.update(
                base + ("." if node.module else "") + alias.name
                for alias in node.names
                if alias.name != "*"
            )
            identifiers.update(alias.name for alias in node.names)
            identifiers.update(alias.asname or alias.name for alias in node.names)
            if node.module in {"importlib", "builtins"}:
                imported_loaders.append(node)
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
            dynamic_calls.append(node)
            call_target = node.func
            if (
                isinstance(call_target, ast.Attribute)
                and isinstance(call_target.value, ast.Name)
                and call_target.value.id in export_tables
            ):
                raise ValueError(f"dynamic package export table: {path}")
    for declaration in imported_loaders:
        dynamic_loaders.update(
            alias.asname or alias.name
            for alias in declaration.names
            if alias.name in {"__import__", "import_module"}
        )
    for node in dynamic_calls:
        call_target = node.func
        if not (
            isinstance(call_target, ast.Name)
            and call_target.id in dynamic_loaders
            or isinstance(call_target, ast.Attribute)
            and call_target.attr == "import_module"
        ):
            continue
        if (
            not node.args
            or not isinstance(node.args[0], ast.Constant)
            or type(node.args[0].value) is not str
        ):
            unknown_dynamic_import = True
            continue
        dynamic_imports.add(node.args[0].value)
        package_argument = next(
            (keyword.value for keyword in node.keywords if keyword.arg == "package"),
            None,
        )
        if (
            package_argument is None
            and node.args[0].value.startswith(".")
            and len(node.args) > 1
        ):
            package_argument = node.args[1]
        if package_argument is None:
            package_name = None
        elif (
            isinstance(package_argument, ast.Constant)
            and type(package_argument.value) is str
        ):
            package_name = package_argument.value
        else:
            package_name = None
            unknown_dynamic_import = True
        dynamic_import_routes.add((node.args[0].value, package_name))
    return SourceSyntax(
        frozenset(identifiers),
        frozenset(imports),
        frozenset(functions),
        frozenset(classes),
        frozenset(exports),
        frozenset(export_modules),
        frozenset(dynamic_imports),
        unknown_dynamic_import,
        frozenset(dynamic_import_routes),
        tuple(import_refs),
    )


def module_package(path: Path, source_root: Path | None = None) -> tuple[str, ...]:
    """Qualified package containing an implementation or package initializer."""
    source_root = SRC if source_root is None else source_root
    relative = path.resolve().relative_to(source_root.resolve())
    return ("number_compiler", *relative.parent.parts)


def _resolved_import_from_names(
    node: ast.ImportFrom, package: tuple[str, ...] | None
) -> tuple[str, ...]:
    """Resolve one from-import, omitting relative names without package context."""
    if node.level and package is None:
        return ()
    if node.level:
        assert package is not None
        keep = max(0, len(package) - node.level + 1)
        base_parts = package[:keep]
    else:
        base_parts = ()
    if node.module:
        base_parts = (*base_parts, *node.module.split("."))
    base = ".".join(base_parts)
    imported = [base] if base else []
    imported.extend(
        ".".join(part for part in (base, alias.name) if part)
        for alias in node.names
        if alias.name != "*"
    )
    return tuple(imported)


def import_references(
    path: Path,
    *,
    source_root: Path | None = None,
    tree: ast.Module | None = None,
) -> tuple[tuple[int, str], ...]:
    """Resolve every syntactic import, retaining source lines and local imports.

    The result includes imports under ``TYPE_CHECKING`` and in function bodies.
    Relative imports are resolved against the importing module's package.
    """
    path = Path(path).resolve()
    source_root = Path(SRC if source_root is None else source_root).resolve()
    package = module_package(path, source_root)
    parsed = tree if tree is not None else _tree(path)
    references: list[tuple[int, str]] = []
    for node in ast.walk(parsed):
        if isinstance(node, ast.Import):
            references.extend((node.lineno, alias.name) for alias in node.names)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        references.extend(
            (node.lineno, imported)
            for imported in _resolved_import_from_names(node, package)
        )
    return tuple(references)


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
    package = module_package(path, SRC)
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
