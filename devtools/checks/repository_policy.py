"""Whole-repository authored-source structural policy checks.

The checks are intentionally iterative: the rule prohibiting direct and mutual
Python recursion applies to the checker itself as well as production code.
"""

from __future__ import annotations

import ast
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

MAX_SOURCE_LINES = 1000
# Isabelle theories are authored source and share the physical line cap.  The
# Python call-graph checker remains intentionally limited to Python modules.
SOURCE_SUFFIXES = frozenset({".py", ".pyi", ".thy"})
IGNORED_PARTS = {
    ".git",
    ".venv",
    "venv",
    "build",
    "dist",
    ".pytest_cache",
    "__pycache__",
    ".mypy_cache",
    ".ruff_cache",
}


@dataclass(frozen=True, slots=True)
class FunctionInfo:
    key: str
    module: str
    qualname: str
    name: str
    parent_qualname: str
    class_qualname: str | None
    node: ast.FunctionDef | ast.AsyncFunctionDef


def _module_name(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    parts = list(rel.parts)
    if parts and parts[0] == "src" and len(parts) >= 2:
        parts = parts[1:]
    if parts and parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def _iter_python_files(root: Path) -> tuple[Path, ...]:
    files: list[Path] = []
    for path in root.rglob("*.py"):
        if any(part in IGNORED_PARTS for part in path.relative_to(root).parts):
            continue
        files.append(path)
    return tuple(sorted(files))


def _parsed_python_sources(root: Path) -> dict[Path, ast.Module]:
    """Parse a fresh repository snapshot for one aggregate policy report."""
    return {
        path: ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for path in _iter_python_files(root)
    }


def physical_line_count(path: Path) -> int:
    """Count physical lines without inventing a line after a final newline.

    Text mode normalizes CRLF and CR endings. Unlike ``str.splitlines()``,
    this does not treat form feeds or Unicode separators as physical newlines.
    """
    text = path.read_text(encoding="utf-8")
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def source_line_violations(
    root: Path,
    limit: int = MAX_SOURCE_LINES,
) -> tuple[tuple[str, int], ...]:
    """Check every authored Python source, including tests and developer tools."""
    violations: list[tuple[str, int]] = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        rel = path.relative_to(root)
        if path.suffix not in SOURCE_SUFFIXES:
            continue
        if any(part in IGNORED_PARTS for part in rel.parts):
            continue
        lines = physical_line_count(path)
        if lines > int(limit):
            violations.append((rel.as_posix(), lines))
    return tuple(violations)


def _function_catalog(
    root: Path,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
) -> tuple[
    dict[str, FunctionInfo],
    dict[str, dict[str, str]],
    dict[tuple[str, str], dict[str, str]],
    dict[tuple[str, str], dict[str, str]],
    dict[str, dict[str, tuple[str, str | None]]],
    dict[str, tuple[ast.Call, ...]],
]:
    functions: dict[str, FunctionInfo] = {}
    module_defs: dict[str, dict[str, str]] = {}
    scope_defs: dict[tuple[str, str], dict[str, str]] = {}
    class_defs: dict[tuple[str, str], dict[str, str]] = {}
    imports: dict[str, dict[str, tuple[str, str | None]]] = {}
    calls: dict[str, list[ast.Call]] = {}

    sources = (
        parsed_sources if parsed_sources is not None else _parsed_python_sources(root)
    )
    for path, tree in sorted(sources.items()):
        module = _module_name(root, path)
        module_defs.setdefault(module, {})
        imports.setdefault(module, {})
        # Stack items carry lexical parent and enclosing class names.  Function
        # bodies are traversed, so nested functions are catalogued too.
        stack: list[tuple[ast.AST, str, str | None, str | None]] = [
            (tree, "", None, None)
        ]
        while stack:
            node, parent_qn, class_qn, active_function = stack.pop()
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qn = f"{parent_qn}.{node.name}" if parent_qn else node.name
                key = f"{module}:{qn}"
                info = FunctionInfo(
                    key, module, qn, node.name, parent_qn, class_qn, node
                )
                functions[key] = info
                calls[key] = []
                scope_defs.setdefault((module, parent_qn), {})[node.name] = key
                if class_qn is not None and parent_qn == class_qn:
                    class_defs.setdefault((module, class_qn), {})[node.name] = key
                if not parent_qn:
                    module_defs[module][node.name] = key
                for child in reversed(node.body):
                    stack.append((child, qn, class_qn, key))
                continue
            if isinstance(node, ast.ClassDef):
                qn = f"{parent_qn}.{node.name}" if parent_qn else node.name
                for child in reversed(node.body):
                    stack.append((child, qn, qn, None))
                continue
            if isinstance(node, ast.Lambda):
                continue
            if isinstance(node, ast.Call) and active_function is not None:
                calls[active_function].append(node)
            import_scope = f"{module}:{parent_qn}" if parent_qn else module
            imports.setdefault(import_scope, {})
            if isinstance(node, ast.Import):
                for alias in node.names:
                    imports[import_scope][alias.asname or alias.name.split(".")[0]] = (
                        alias.name,
                        None,
                    )
            elif isinstance(node, ast.ImportFrom):
                base = node.module or ""
                if node.level:
                    mod_parts = module.split(".")[:-1]
                    keep = max(0, len(mod_parts) - (node.level - 1))
                    prefix = mod_parts[:keep]
                    base = ".".join(prefix + ([base] if base else []))
                for alias in node.names:
                    if alias.name != "*":
                        imports[import_scope][alias.asname or alias.name] = (
                            base,
                            alias.name,
                        )
            for descendant in reversed(tuple(ast.iter_child_nodes(node))):
                stack.append((descendant, parent_qn, class_qn, active_function))
    return (
        functions,
        module_defs,
        scope_defs,
        class_defs,
        imports,
        {key: tuple(items) for key, items in calls.items()},
    )


def _resolve_name(
    info: FunctionInfo,
    name: str,
    module_defs: dict[str, dict[str, str]],
    scope_defs: dict[tuple[str, str], dict[str, str]],
    imports: dict[str, dict[str, tuple[str, str | None]]],
) -> str | None:
    # Search nested lexical scopes from the current function outward.
    qn = info.qualname
    while True:
        local_import = imports.get(f"{info.module}:{qn}", {}).get(name)
        if local_import is not None:
            imported_module, imported_symbol = local_import
            if imported_symbol is not None:
                return module_defs.get(imported_module, {}).get(imported_symbol)
            return None
        target = scope_defs.get((info.module, qn), {}).get(name)
        if target is not None:
            return target
        if "." not in qn:
            break
        qn = qn.rsplit(".", 1)[0]
    target = scope_defs.get((info.module, info.parent_qualname), {}).get(name)
    if target is not None:
        return target
    target = module_defs.get(info.module, {}).get(name)
    if target is not None:
        return target
    imported = imports.get(info.module, {}).get(name)
    if imported is not None and imported[1] is not None:
        mod, symbol = imported
        assert symbol is not None
        return module_defs.get(mod, {}).get(symbol)
    return None


def recursion_cycles(
    root: Path,
    *,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
) -> tuple[tuple[str, ...], ...]:
    """Return exact statically-resolved direct/mutual recursion SCCs."""
    functions, module_defs, scope_defs, class_defs, imports, calls = _function_catalog(
        root, parsed_sources
    )
    graph: dict[str, set[str]] = {key: set() for key in functions}
    for key, info in functions.items():
        for call in calls[key]:
            fn = call.func
            target: str | None = None
            if isinstance(fn, ast.Name):
                target = _resolve_name(info, fn.id, module_defs, scope_defs, imports)
            elif isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name):
                owner = fn.value.id
                if (
                    owner in ("self", "cls")
                    and info.class_qualname is not None
                    or info.class_qualname is not None
                    and owner == info.class_qualname.rsplit(".", 1)[-1]
                ):
                    target = class_defs.get((info.module, info.class_qualname), {}).get(
                        fn.attr
                    )
                else:
                    imported = imports.get(info.module, {}).get(owner)
                    if imported is not None and imported[1] is None:
                        target = module_defs.get(imported[0], {}).get(fn.attr)
            if target in graph:
                graph[key].add(target)

    # Iterative Kosaraju: first produce reverse postorder.
    seen: set[str] = set()
    finish: list[str] = []
    for root_key_1 in sorted(graph):
        if root_key_1 in seen:
            continue
        stack: list[tuple[str, bool]] = [(root_key_1, False)]
        while stack:
            node, expanded = stack.pop()
            if expanded:
                finish.append(node)
                continue
            if node in seen:
                continue
            seen.add(node)
            stack.append((node, True))
            for child in sorted(graph[node], reverse=True):
                if child not in seen:
                    stack.append((child, False))

    reverse: dict[str, set[str]] = {key: set() for key in graph}
    for source, targets in graph.items():
        for target in targets:
            reverse[target].add(source)

    assigned: set[str] = set()
    cycles: list[tuple[str, ...]] = []
    for root_key_2 in reversed(finish):
        if root_key_2 in assigned:
            continue
        component: list[str] = []
        reverse_stack = [root_key_2]
        assigned.add(root_key_2)
        while reverse_stack:
            node = reverse_stack.pop()
            component.append(node)
            for parent in reverse[node]:
                if parent not in assigned:
                    assigned.add(parent)
                    reverse_stack.append(parent)
        if len(component) > 1 or (
            len(component) == 1 and component[0] in graph[component[0]]
        ):
            cycles.append(tuple(sorted(component)))
    return tuple(sorted(cycles))


def repository_policy_report(root: Path) -> dict[str, object]:
    from devtools.checks.package_contracts import package_violations

    root = Path(root).resolve()
    parsed_sources = _parsed_python_sources(root)
    return {
        "max_source_lines": MAX_SOURCE_LINES,
        "source_line_violations": source_line_violations(root),
        "recursion_cycles": recursion_cycles(root, parsed_sources=parsed_sources),
        "package_violations": package_violations(root, parsed_sources=parsed_sources),
    }


__all__ = [
    "MAX_SOURCE_LINES",
    "SOURCE_SUFFIXES",
    "physical_line_count",
    "recursion_cycles",
    "repository_policy_report",
    "source_line_violations",
]


def main() -> int:
    """Report all structural failures without mutating source."""
    import json

    from devtools.paths import repository_root

    report = repository_policy_report(repository_root())
    print(json.dumps(report, indent=2))
    return int(
        bool(
            report["source_line_violations"]
            or report["recursion_cycles"]
            or report["package_violations"]
        )
    )


if __name__ == "__main__":
    raise SystemExit(main())
