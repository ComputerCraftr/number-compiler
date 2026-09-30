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
SOURCE_SUFFIXES = frozenset({".py", ".pyi", ".thy", ".ML", ".sml"})
SOURCE_FILENAMES = frozenset({"ROOT", "ROOTS"})
IGNORED_PARTS = {
    ".git",
    ".venv",
    ".pytest_cache",
    "__pycache__",
    ".mypy_cache",
    ".ruff_cache",
}
IGNORED_ROOTS = {"results", "build", "dist", "venv"}


@dataclass(frozen=True, slots=True)
class FunctionInfo:
    key: str
    module: str
    qualname: str
    name: str
    parent_qualname: str
    class_qualname: str | None
    node: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda


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
        if _ignored_source_path(path.relative_to(root)):
            continue
        files.append(path)
    return tuple(sorted(files))


def _ignored_source_path(relative: Path) -> bool:
    """Generated roots cannot hide authored modules with the same basename."""
    return relative.parts[0] in IGNORED_ROOTS or any(
        part in IGNORED_PARTS for part in relative.parts
    )


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
        if path.suffix not in SOURCE_SUFFIXES and path.name not in SOURCE_FILENAMES:
            continue
        if _ignored_source_path(rel):
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
    dict[str, dict[str, list[ast.expr]]],
    dict[str, tuple[ast.Call, ...]],
]:
    functions: dict[str, FunctionInfo] = {}
    module_defs: dict[str, dict[str, str]] = {}
    scope_defs: dict[tuple[str, str], dict[str, str]] = {}
    class_defs: dict[tuple[str, str], dict[str, str]] = {}
    imports: dict[str, dict[str, tuple[str, str | None]]] = {}
    module_aliases: dict[str, dict[str, list[ast.expr]]] = {}
    calls: dict[str, list[ast.Call]] = {}

    sources = (
        parsed_sources if parsed_sources is not None else _parsed_python_sources(root)
    )
    for path, tree in sorted(sources.items()):
        module = _module_name(root, path)
        module_defs.setdefault(module, {})
        imports.setdefault(module, {})
        module_aliases.setdefault(module, {})
        lambda_names: dict[ast.Lambda, tuple[str, ...]] = {}
        for statement in ast.walk(tree):
            if isinstance(statement, (ast.Assign, ast.AnnAssign)) and isinstance(
                statement.value, ast.Lambda
            ):
                targets = (
                    statement.targets
                    if isinstance(statement, ast.Assign)
                    else [statement.target]
                )
                lambda_names[statement.value] = tuple(
                    target.id for target in targets if isinstance(target, ast.Name)
                )
        # Stack items carry lexical parent and enclosing class names.  Function
        # bodies are traversed, so nested functions are catalogued too.
        stack: list[tuple[ast.AST, str, str | None, str | None]] = [
            (tree, "", None, None)
        ]
        while stack:
            node, parent_qn, class_qn, active_function = stack.pop()
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                if active_function is not None and not isinstance(node, ast.Lambda):
                    expressions: list[ast.AST] = [
                        *node.decorator_list,
                        *node.args.defaults,
                        *(default for default in node.args.kw_defaults if default),
                    ]
                    if node.returns is not None:
                        expressions.append(node.returns)
                    expression_stack = expressions
                    while expression_stack:
                        expression = expression_stack.pop()
                        if isinstance(
                            expression,
                            (
                                ast.FunctionDef,
                                ast.AsyncFunctionDef,
                                ast.ClassDef,
                                ast.Lambda,
                            ),
                        ):
                            continue
                        if isinstance(expression, ast.Call):
                            calls[active_function].append(expression)
                        expression_stack.extend(ast.iter_child_nodes(expression))
                names = (
                    lambda_names.get(node, ())
                    if isinstance(node, ast.Lambda)
                    else (node.name,)
                )
                name = (
                    names[0] if names else f"<lambda@{node.lineno}:{node.col_offset}>"
                )
                qn = f"{parent_qn}.{name}" if parent_qn else name
                key = f"{module}:{qn}"
                info = FunctionInfo(key, module, qn, name, parent_qn, class_qn, node)
                functions[key] = info
                calls[key] = []
                for name in names:
                    scope_defs.setdefault((module, parent_qn), {})[name] = key
                    if class_qn is not None and parent_qn == class_qn:
                        class_defs.setdefault((module, class_qn), {})[name] = key
                    if not parent_qn:
                        module_defs[module][name] = key
                body = [node.body] if isinstance(node, ast.Lambda) else node.body
                for child in reversed(body):
                    stack.append((child, qn, class_qn, key))
                continue
            if isinstance(node, ast.ClassDef):
                qn = f"{parent_qn}.{node.name}" if parent_qn else node.name
                for child in reversed(node.body):
                    stack.append((child, qn, qn, None))
                continue
            if isinstance(node, ast.Call) and active_function is not None:
                calls[active_function].append(node)
            if active_function is None and not parent_qn:
                if isinstance(node, ast.Assign) and node.value is not None:
                    for target in node.targets:
                        for name, value in _assignment_bindings(target, node.value):
                            module_aliases[module].setdefault(name, []).append(value)
                elif isinstance(node, ast.AnnAssign) and node.value is not None:
                    for name, value in _assignment_bindings(node.target, node.value):
                        module_aliases[module].setdefault(name, []).append(value)
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
        module_aliases,
        {key: tuple(items) for key, items in calls.items()},
    )


def _resolve_name(
    info: FunctionInfo,
    name: str,
    module_defs: dict[str, dict[str, str]],
    scope_defs: dict[tuple[str, str], dict[str, str]],
    imports: dict[str, dict[str, tuple[str, str | None]]],
    module_aliases: dict[str, dict[str, list[ast.expr]]],
    scope_aliases: dict[tuple[str, str], dict[str, list[ast.expr]]],
    scope_bound: dict[tuple[str, str], set[str]],
) -> str | None:
    pending: list[tuple[str, str]] = [(info.qualname, name)]
    visited: set[tuple[str, str]] = set()
    while pending:
        qn, symbol = pending.pop()
        if (qn, symbol) in visited:
            continue
        visited.add((qn, symbol))
        if qn:
            local_import = imports.get(f"{info.module}:{qn}", {}).get(symbol)
            if local_import is not None:
                imported_module, imported_symbol = local_import
                if imported_symbol is not None:
                    target = module_defs.get(imported_module, {}).get(imported_symbol)
                    if target is not None:
                        return target
                continue
            is_class_scope = qn == info.class_qualname
            if not is_class_scope:
                target = scope_defs.get((info.module, qn), {}).get(symbol)
                if target is not None:
                    return target
                for value in scope_aliases.get((info.module, qn), {}).get(symbol, ()):
                    if isinstance(value, ast.Name):
                        pending.append((qn, value.id))
                if symbol in scope_bound.get((info.module, qn), set()):
                    continue
            if "." in qn:
                pending.append((qn.rsplit(".", 1)[0], symbol))
                continue
            pending.append(("", symbol))
            continue
        target = module_defs.get(info.module, {}).get(symbol)
        if target is not None:
            return target
        for value in module_aliases.get(info.module, {}).get(symbol, ()):
            if isinstance(value, ast.Name):
                pending.append(("", value.id))
        imported = imports.get(info.module, {}).get(symbol)
        if imported is not None and imported[1] is not None:
            mod, imported_symbol = imported
            assert imported_symbol is not None
            target = module_defs.get(mod, {}).get(imported_symbol)
            if target is not None:
                return target
    return None


def _resolve_import(
    info: FunctionInfo,
    name: str,
    imports: dict[str, dict[str, tuple[str, str | None]]],
) -> tuple[str, str | None] | None:
    """Find an import binding in the current lexical scope chain."""
    qn = info.qualname
    while True:
        imported = imports.get(f"{info.module}:{qn}", {}).get(name)
        if imported is not None:
            return imported
        if "." not in qn:
            break
        qn = qn.rsplit(".", 1)[0]
    return imports.get(info.module, {}).get(name)


def _assignment_bindings(
    target: ast.expr,
    value: ast.expr,
) -> list[tuple[str, ast.expr]]:
    """Pair statically destructured names with their assigned expressions."""
    bindings: list[tuple[str, ast.expr]] = []
    pending: list[tuple[ast.expr, ast.expr]] = [(target, value)]
    while pending:
        current_target, current_value = pending.pop()
        if isinstance(current_target, ast.Name):
            bindings.append((current_target.id, current_value))
            continue
        if isinstance(current_target, ast.Starred):
            continue
        if (
            isinstance(current_target, (ast.List, ast.Tuple))
            and isinstance(current_value, (ast.List, ast.Tuple))
            and len(current_target.elts) == len(current_value.elts)
        ):
            pending.extend(zip(current_target.elts, current_value.elts, strict=True))
    return bindings


def _name_aliases(name: str, aliases: dict[str, list[ast.expr]]) -> set[str]:
    """Return names reachable through direct local name aliases."""
    names: set[str] = set()
    pending = [name]
    while pending:
        current = pending.pop()
        if current in names:
            continue
        names.add(current)
        for value in aliases.get(current, ()):
            if isinstance(value, ast.Name):
                pending.append(value.id)
    return names


def _target_names(target: ast.expr) -> set[str]:
    names: set[str] = set()
    pending: list[ast.expr] = [target]
    while pending:
        node = pending.pop()
        if isinstance(node, ast.Name):
            names.add(node.id)
        elif isinstance(node, ast.Starred):
            pending.append(node.value)
        elif isinstance(node, (ast.List, ast.Tuple)):
            pending.extend(node.elts)
    return names


def _pattern_names(pattern: ast.pattern) -> set[str]:
    names: set[str] = set()
    pending: list[ast.AST] = [pattern]
    while pending:
        node = pending.pop()
        if isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name:
            names.add(node.name)
        elif isinstance(node, ast.MatchMapping) and node.rest:
            names.add(node.rest)
        pending.extend(ast.iter_child_nodes(node))
    return names


def _call_aliases(
    info: FunctionInfo,
) -> tuple[dict[str, list[ast.expr]], set[str], dict[ast.Call, frozenset[str]]]:
    """Resolve local callable aliases without treating parameters as globals."""
    args = info.node.args
    bound = {arg.arg for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs)}
    bound.update(arg.arg for arg in (args.vararg, args.kwarg) if arg is not None)
    declared_global: set[str] = set()
    declared_nonlocal: set[str] = set()
    aliases: dict[str, list[ast.expr]] = {}
    comprehension_bindings: dict[ast.Call, frozenset[str]] = {}
    body = [info.node.body] if isinstance(info.node, ast.Lambda) else info.node.body
    pending: list[tuple[ast.AST, frozenset[str]]] = [
        (node, frozenset()) for node in body
    ]
    while pending:
        node, comprehension_bound = pending.pop()
        if isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
        ):
            continue
        if isinstance(
            node, (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
        ):
            operations: list[tuple[ast.AST, frozenset[str]]] = []
            current = set(comprehension_bound)
            for generator in node.generators:
                operations.append((generator.iter, frozenset(current)))
                current.update(_target_names(generator.target))
                operations.extend(
                    (condition, frozenset(current)) for condition in generator.ifs
                )
            outputs = (
                (node.key, node.value)
                if isinstance(node, ast.DictComp)
                else (node.elt,)
            )
            operations.extend((output, frozenset(current)) for output in outputs)
            pending.extend(reversed(operations))
            continue
        if isinstance(node, ast.ExceptHandler):
            if node.name:
                bound.add(node.name)
            if node.type is not None:
                pending.append((node.type, comprehension_bound))
            handler_bound = comprehension_bound | ({node.name} if node.name else set())
            pending.extend((child, handler_bound) for child in reversed(node.body))
            continue
        if isinstance(node, ast.Match):
            pending.append((node.subject, comprehension_bound))
            for case in reversed(node.cases):
                pattern_bound = _pattern_names(case.pattern)
                bound.update(pattern_bound)
                case_bound = comprehension_bound | pattern_bound
                pending.extend((child, case_bound) for child in reversed(case.body))
                if case.guard is not None:
                    pending.append((case.guard, case_bound))
            continue
        if isinstance(node, ast.IfExp):
            pending.append((node.body, comprehension_bound))
            pending.append((node.orelse, comprehension_bound))
            continue
        if isinstance(node, ast.Call):
            comprehension_bindings[node] = comprehension_bound
        if isinstance(node, ast.Global):
            declared_global.update(node.names)
            continue
        if isinstance(node, ast.Nonlocal):
            declared_nonlocal.update(node.names)
            continue
        if isinstance(node, ast.comprehension):
            # Comprehension targets live in the comprehension's implicit scope.
            pending.extend((condition, comprehension_bound) for condition in node.ifs)
            pending.append((node.iter, comprehension_bound))
            continue
        if isinstance(node, ast.Assign) and node.value is not None:
            for target in node.targets:
                for name, value in _assignment_bindings(target, node.value):
                    aliases.setdefault(name, []).append(value)
        elif (
            isinstance(node, (ast.AnnAssign, ast.NamedExpr)) and node.value is not None
        ):
            for name, value in _assignment_bindings(node.target, node.value):
                aliases.setdefault(name, []).append(value)
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            bound.add(node.id)
        pending.extend(
            (child, comprehension_bound) for child in ast.iter_child_nodes(node)
        )
    bound.difference_update(declared_global | declared_nonlocal)
    return aliases, bound, comprehension_bindings


def recursion_cycles(
    root: Path,
    *,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
) -> tuple[tuple[str, ...], ...]:
    """Return exact statically-resolved direct/mutual recursion SCCs."""
    (
        functions,
        module_defs,
        scope_defs,
        class_defs,
        imports,
        module_aliases,
        calls,
    ) = _function_catalog(root, parsed_sources)
    graph: dict[str, set[str]] = {key: set() for key in functions}
    lambda_keys = {
        info.node: key
        for key, info in functions.items()
        if isinstance(info.node, ast.Lambda)
    }
    analyses: dict[
        str, tuple[dict[str, list[ast.expr]], set[str], dict[ast.Call, frozenset[str]]]
    ] = {}
    scope_aliases: dict[tuple[str, str], dict[str, list[ast.expr]]] = {}
    scope_bound: dict[tuple[str, str], set[str]] = {}
    for key, info in functions.items():
        analysis = _call_aliases(info)
        analyses[key] = analysis
        scope_aliases[(info.module, info.qualname)] = analysis[0]
        scope_bound[(info.module, info.qualname)] = analysis[1]
    for key, info in functions.items():
        aliases, bound, comprehension_bindings = analyses[key]
        for call in calls[key]:
            call_bound = bound | comprehension_bindings.get(call, frozenset())
            pending = [call.func]
            visited: set[ast.expr] = set()
            while pending:
                fn = pending.pop()
                if fn in visited:
                    continue
                visited.add(fn)
                if (
                    isinstance(fn, ast.Name)
                    and fn.id in aliases
                    and fn.id not in comprehension_bindings.get(call, frozenset())
                ):
                    for alias in aliases[fn.id]:
                        if isinstance(alias, ast.Name) and alias.id == fn.id:
                            target = _resolve_call(
                                info,
                                alias,
                                aliases,
                                call_bound,
                                module_defs,
                                scope_defs,
                                class_defs,
                                imports,
                                lambda_keys,
                                module_aliases,
                                scope_aliases,
                                scope_bound,
                            )
                            if target in graph:
                                graph[key].add(target)
                        else:
                            pending.append(alias)
                    continue
                if isinstance(fn, ast.NamedExpr):
                    pending.append(fn.value)
                    continue
                if isinstance(fn, ast.IfExp):
                    pending.append(fn.body)
                    pending.append(fn.orelse)
                    continue
                target = _resolve_call(
                    info,
                    fn,
                    aliases,
                    call_bound,
                    module_defs,
                    scope_defs,
                    class_defs,
                    imports,
                    lambda_keys,
                    module_aliases,
                    scope_aliases,
                    scope_bound,
                )
                if target in graph:
                    graph[key].add(target)

    return _cycles(graph)


def _resolve_call(
    info: FunctionInfo,
    fn: ast.expr,
    aliases: dict[str, list[ast.expr]],
    bound: set[str],
    module_defs: dict[str, dict[str, str]],
    scope_defs: dict[tuple[str, str], dict[str, str]],
    class_defs: dict[tuple[str, str], dict[str, str]],
    imports: dict[str, dict[str, tuple[str, str | None]]],
    lambda_keys: dict[ast.Lambda, str],
    module_aliases: dict[str, dict[str, list[ast.expr]]],
    scope_aliases: dict[tuple[str, str], dict[str, list[ast.expr]]],
    scope_bound: dict[tuple[str, str], set[str]],
) -> str | None:
    target: str | None = None
    if isinstance(fn, ast.Name):
        if fn.id not in bound:
            target = _resolve_name(
                info,
                fn.id,
                module_defs,
                scope_defs,
                imports,
                module_aliases,
                scope_aliases,
                scope_bound,
            )
    elif isinstance(fn, ast.Lambda):
        target = lambda_keys.get(fn)
    elif isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name):
        owner = fn.value.id
        owner_names = _name_aliases(owner, aliases)
        receiver = None
        if info.parent_qualname == info.class_qualname:
            arguments = (*info.node.args.posonlyargs, *info.node.args.args)
            static = not isinstance(info.node, ast.Lambda) and any(
                isinstance(decorator, ast.Name) and decorator.id == "staticmethod"
                for decorator in info.node.decorator_list
            )
            if arguments and not static:
                receiver = arguments[0].arg
        receiver_names = owner_names.intersection((receiver,)) if receiver else set()
        if receiver in aliases and owner == receiver:
            receiver_names.discard(receiver)
        class_name = (
            info.class_qualname.rsplit(".", 1)[-1] if info.class_qualname else None
        )
        class_name_match = (
            class_name is not None
            and class_name in owner_names
            and class_name not in bound
        )
        if info.class_qualname is not None and (receiver_names or class_name_match):
            target = class_defs.get((info.module, info.class_qualname), {}).get(fn.attr)
        else:
            if owner not in bound:
                target = class_defs.get((info.module, owner), {}).get(fn.attr)
            for owner_name in sorted(owner_names):
                if owner_name == owner and owner in bound:
                    continue
                imported = _resolve_import(info, owner_name, imports)
                if imported is not None and imported[1] is None:
                    target = module_defs.get(imported[0], {}).get(fn.attr)
                    if target is not None:
                        break
    return target


def _cycles(graph: dict[str, set[str]]) -> tuple[tuple[str, ...], ...]:
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
    from dataclasses import asdict

    from devtools.checks.package_contracts import package_violations
    from devtools.checks.python_clones import (
        MIN_CLONE_NODES,
        MIN_CLONE_STATEMENTS,
        MIN_SINGLE_STATEMENT_OPERATIONS,
        duplicate_bodies,
    )

    root = Path(root).resolve()
    parsed_sources = _parsed_python_sources(root)
    return {
        "max_source_lines": MAX_SOURCE_LINES,
        "clone_minimum_expression_statement_nodes": MIN_CLONE_NODES,
        "clone_minimum_statements": MIN_CLONE_STATEMENTS,
        "clone_minimum_single_statement_operations": MIN_SINGLE_STATEMENT_OPERATIONS,
        "source_line_violations": source_line_violations(root),
        "recursion_cycles": recursion_cycles(root, parsed_sources=parsed_sources),
        "duplicate_bodies": tuple(
            tuple(asdict(site) for site in group)
            for group in duplicate_bodies(root, parsed_sources)
        ),
        "package_violations": package_violations(root, parsed_sources=parsed_sources),
    }


__all__ = [
    "MAX_SOURCE_LINES",
    "SOURCE_FILENAMES",
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
            or report["duplicate_bodies"]
            or report["package_violations"]
        )
    )


if __name__ == "__main__":
    raise SystemExit(main())
