"""AST/file helpers for the canonical compiler architecture audit."""

from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path
from typing import TypeGuard

from devtools.paths import repository_root

ROOT = repository_root()
SRC = ROOT / "src" / "number_compiler"


def _object_sequence(value: object) -> TypeGuard[list[object] | tuple[object, ...]]:
    return type(value) in {list, tuple}


def _object_dictionary(value: object) -> TypeGuard[dict[object, object]]:
    return type(value) is dict


def _exact_string(value: object) -> TypeGuard[str]:
    return type(value) is str


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
            literal: object = ast.literal_eval(statement.value)
        except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
            # Nonliteral export tables require a separate dynamic audit.
            raise ValueError(f"nonliteral package export table: {path}") from None
        if "__all__" in assigned:
            if not _object_sequence(literal):
                raise ValueError(f"invalid __all__ export table: {path}")
            for item in literal:
                if not _exact_string(item):
                    raise ValueError(f"invalid __all__ export table: {path}")
                exports.add(item)
        if "_EXPORT_MODULES" in assigned:
            if not _object_dictionary(literal):
                raise ValueError(f"invalid lazy export table: {path}")
            for key, value in literal.items():
                if not _exact_string(key) or not _exact_string(value):
                    raise ValueError(f"invalid lazy export table: {path}")
                exports.add(key)
                export_modules.add(value)
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
