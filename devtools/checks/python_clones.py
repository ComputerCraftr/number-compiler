"""Binding-aware Python clone detection, without importing audited modules.

A substantial clone has 24 expression/statement nodes and either three executable
statements or a single statement with three computational operations. Check
complete bodies and three-statement windows, including
nested suites. This is structural alpha equivalence, not arbitrary semantic
equivalence: literals, operators, attribute names and free names remain exact.
There are no path allowlists, suppressions or historical clone baselines.
"""

from __future__ import annotations

import ast
import hashlib
import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path

MIN_CLONE_NODES = 24
MIN_CLONE_STATEMENTS = 3
MIN_SINGLE_STATEMENT_OPERATIONS = 3
_OPERATIONS = (
    ast.BinOp,
    ast.UnaryOp,
    ast.BoolOp,
    ast.Compare,
    ast.IfExp,
    ast.comprehension,
)
_FUNCTIONS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_IGNORED_FIELDS = frozenset({"annotation", "returns", "type_comment", "type_params"})
_BINDING_FIELDS = {
    ast.arg: "arg",
    ast.FunctionDef: "name",
    ast.AsyncFunctionDef: "name",
    ast.ClassDef: "name",
    ast.ExceptHandler: "name",
    ast.MatchAs: "name",
    ast.MatchStar: "name",
    ast.MatchMapping: "rest",
    ast.alias: "asname",
}


@dataclass(eq=False)
class _Scope:
    parent: _Scope | None
    kind: str
    bound: set[str] = field(default_factory=set)
    globals: set[str] = field(default_factory=set)
    nonlocals: set[str] = field(default_factory=set)


def _children(node: ast.AST) -> list[ast.AST]:
    children = []
    for name, value in ast.iter_fields(node):
        if name in _IGNORED_FIELDS:
            continue
        if isinstance(value, ast.AST):
            children.append(value)
        elif isinstance(value, list):
            children.extend(item for item in value if isinstance(item, ast.AST))
    return children


class _Bindings:
    """Lexical owners and bindings for one source file and its nested scopes."""

    def __init__(self, root: ast.Module) -> None:
        self.owner: dict[ast.AST, _Scope] = {}
        self.inner: dict[ast.AST, _Scope] = {}
        outer = _Scope(None, "external")
        pending: list[tuple[ast.AST, _Scope]] = [(root, outer)]
        while pending:
            node, scope = pending.pop()
            self.owner[node] = scope
            children = [(child, scope) for child in _children(node)]
            if isinstance(node, (*_FUNCTIONS, ast.ClassDef, *_COMPREHENSIONS)):
                kind = (
                    "class"
                    if isinstance(node, ast.ClassDef)
                    else "comprehension"
                    if isinstance(node, _COMPREHENSIONS)
                    else "function"
                )
                inner = _Scope(scope, kind)
                self.inner[node] = inner
                if isinstance(
                    node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
                ):
                    scope.bound.add(node.name)
                    body = set(node.body)
                    children = [
                        (child, inner if child in body else scope)
                        for child, _ in children
                    ]
                if isinstance(node, _FUNCTIONS):
                    children = [
                        (child, inner if child is node.args else owner)
                        for child, owner in children
                    ]
                    if isinstance(node, ast.Lambda):
                        children = [
                            (child, inner if child is node.body else owner)
                            for child, owner in children
                        ]
                    # Defaults execute in the enclosing scope, not in the body.
                    defaults = {*node.args.defaults, *node.args.kw_defaults} - {None}
                    self.owner[node.args] = inner
                    children = [
                        (child, owner)
                        for child, owner in children
                        if child is not node.args
                    ]
                    children.extend(
                        (child, scope if child in defaults else inner)
                        for child in _children(node.args)
                    )
                if isinstance(node, _COMPREHENSIONS):
                    children = [(child, inner) for child, _ in children]
                    # The first iterable is evaluated outside the comprehension.
                    first = node.generators[0]
                    children = [
                        (child, owner)
                        for child, owner in children
                        if child is not first
                    ]
                    self.owner[first] = inner
                    children.extend(
                        (child, scope if child is first.iter else inner)
                        for child in _children(first)
                    )
            if isinstance(node, ast.NamedExpr):
                target_scope = scope
                while (
                    target_scope.kind == "comprehension"
                    and target_scope.parent is not None
                ):
                    target_scope = target_scope.parent
                children = [
                    (child, target_scope if child is node.target else owner)
                    for child, owner in children
                ]
            if isinstance(node, ast.Global):
                scope.globals.update(node.names)
            elif isinstance(node, ast.Nonlocal):
                scope.nonlocals.update(node.names)
            elif isinstance(node, ast.Name) and isinstance(
                node.ctx, (ast.Store, ast.Del)
            ):
                scope.bound.add(node.id)
            elif isinstance(node, ast.arg):
                scope.bound.add(node.arg)
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names:
                    scope.bound.add(alias.asname or alias.name.split(".")[0])
            elif (
                isinstance(node, ast.ExceptHandler)
                and node.name is not None
                or (
                    isinstance(node, (ast.MatchAs, ast.MatchStar))
                    and node.name is not None
                )
            ):
                scope.bound.add(node.name)
            elif isinstance(node, ast.MatchMapping) and node.rest is not None:
                scope.bound.add(node.rest)
            pending.extend(reversed(children))
        self.parameters: dict[tuple[_Scope | None, str], int] = {}
        for function in self.inner:
            if not isinstance(function, _FUNCTIONS):
                continue
            args = function.args
            parameters = [*args.posonlyargs, *args.args]
            if args.vararg is not None:
                parameters.append(args.vararg)
            parameters.extend(args.kwonlyargs)
            if args.kwarg is not None:
                parameters.append(args.kwarg)
            self.parameters.update(
                (self.resolve(arg, arg.arg), index)
                for index, arg in enumerate(parameters)
            )

        # Captured locals retain their declaration position in the owner scope,
        # even when a nested body references only one of several owner bindings.
        self.local_positions: dict[tuple[_Scope | None, str], int] = {}
        counts: dict[_Scope, int] = {}
        for node in self.owner:
            field_name = _BINDING_FIELDS.get(type(node))
            name = getattr(node, field_name, None) if field_name else None
            if isinstance(node, ast.Name) and isinstance(
                node.ctx, (ast.Store, ast.Del)
            ):
                name = node.id
            elif isinstance(node, ast.alias):
                name = node.asname or node.name.split(".")[0]
            if not isinstance(name, str):
                continue
            binding = self.resolve(node, name)
            owner = binding[0]
            if (
                owner is None
                or binding in self.parameters
                or binding in self.local_positions
            ):
                continue
            self.local_positions[binding] = counts.get(owner, 0)
            counts[owner] = counts.get(owner, 0) + 1

    def resolve(self, node: ast.AST, name: str) -> tuple[_Scope | None, str]:
        start = self.owner[node]
        scope: _Scope | None = start
        while scope is not None:
            if name in scope.globals:
                return None, name
            if name in scope.bound and name not in scope.nonlocals:
                if scope.kind in {"external", "class"}:
                    return None, name
                return scope, name
            scope = scope.parent
            # Methods/closures do not capture class namespace attributes.
            if scope is not None and scope.kind == "class" and start.kind != "class":
                scope = scope.parent
        return None, name


def _without_docstring(body: Sequence[ast.stmt]) -> list[ast.stmt]:
    if body and isinstance(body[0], ast.Expr):
        value = body[0].value
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return list(body[1:])
    return list(body)


def _identifier(
    node: ast.AST,
    name: str,
    bindings: _Bindings,
    names: dict[tuple[_Scope | None, str], int],
    scope: _Scope,
    captures: Mapping[_Scope, int],
) -> str:
    binding = bindings.resolve(node, name)
    if binding[0] is scope and binding in bindings.parameters:
        return f"parameter:{bindings.parameters[binding]}"
    if binding[0] is not None and binding[0] in captures:
        prefix = f"capture:{captures[binding[0]]}:"
        if binding in bindings.parameters:
            return prefix + f"parameter:{bindings.parameters[binding]}"
        return prefix + f"local:{bindings.local_positions[binding]}"
    if binding[0] is not None:
        return f"local:{names.setdefault(binding, len(names))}"
    return f"free:{name!r}"


def _tokens(
    body: Sequence[ast.stmt],
    bindings: _Bindings,
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
) -> tuple[tuple[str, ...], int, int, int]:
    tokens: list[str] = []
    names: dict[tuple[_Scope | None, str], int] = {}
    scope = bindings.inner[function]
    captures: dict[_Scope, int] = {}
    parent, depth = scope.parent, 0
    while parent is not None:
        if parent.kind in {"function", "comprehension"}:
            depth += 1
            captures[parent] = depth
        parent = parent.parent
    pending: list[object] = [list(body)]
    nodes = statements = operations = 0
    while pending:
        value = pending.pop()
        if isinstance(value, ast.Name):
            nodes += 1
            tokens.append(
                f"Name:{_identifier(value, value.id, bindings, names, scope, captures)}:{type(value.ctx).__name__}"
            )
            continue
        if isinstance(value, ast.Constant):
            nodes += 1
            tokens.append(
                f"Constant:{type(value.value).__name__}:{value.value!r}:{value.kind!r}"
            )
            continue
        if isinstance(value, ast.AST):
            nodes += isinstance(value, (ast.stmt, ast.expr))
            operations += isinstance(value, _OPERATIONS)
            statements += isinstance(value, ast.stmt) and not isinstance(
                value, ast.Pass
            )
            tokens.append(type(value).__name__)
            fields: list[object] = []
            binding_field = _BINDING_FIELDS.get(type(value))
            for name, item in ast.iter_fields(value):
                if name in _IGNORED_FIELDS:
                    continue
                if isinstance(value, ast.alias) and name == "asname":
                    item = value.asname or value.name.split(".")[0]
                if name == binding_field and isinstance(item, str):
                    item = _identifier(value, item, bindings, names, scope, captures)
                if isinstance(value, ast.Nonlocal) and name == "names":
                    item = [
                        _identifier(value, identifier, bindings, names, scope, captures)
                        for identifier in value.names
                    ]
                if (
                    name == "body"
                    and isinstance(item, list)
                    and isinstance(value, (*_FUNCTIONS, ast.ClassDef))
                ):
                    item = _without_docstring(item)
                # AST type fixes the field order; repeated field names carry no
                # additional identity. Lists and optional values remain tagged.
                fields.append(item)
            pending.extend(reversed(fields))
        elif isinstance(value, list):
            tokens.append(f"list:{len(value)}")
            pending.extend(reversed(value))
        else:
            tokens.append(f"{type(value).__name__}:{value!r}")
    return tuple(tokens), nodes, statements, operations


@dataclass(frozen=True, order=True)
class CloneSite:
    path: str
    line: int
    end_line: int
    function: str
    column: int = 0
    end_column: int = 0


@dataclass
class _Candidate:
    site: CloneSite
    canonical: bytes
    size: int


def _bodies(
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
) -> list[list[ast.stmt]]:
    """Complete suites plus fixed windows; never enumerate all interval pairs."""
    if isinstance(function, ast.Lambda):
        # Reuse the original expression nodes and lexical owners. Only the
        # implicit return is synthetic, allowing comparison with def bodies.
        return [[ast.copy_location(ast.Return(value=function.body), function.body)]]
    bodies: list[list[ast.stmt]] = []
    pending: list[ast.AST] = [function]
    while pending:
        node = pending.pop()
        if node is not function and isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
        ):
            continue  # These have their own function inventory.
        for _name, value in ast.iter_fields(node):
            if (
                isinstance(value, list)
                and value
                and all(isinstance(x, ast.stmt) for x in value)
            ):
                body = _without_docstring(value) if node is function else value
                if body:
                    bodies.append(body)
                if len(body) > MIN_CLONE_STATEMENTS:
                    bodies.extend(
                        body[i : i + MIN_CLONE_STATEMENTS]
                        for i in range(len(body) - MIN_CLONE_STATEMENTS + 1)
                    )
        pending.extend(reversed(_children(node)))
    return bodies


def _substantial_bodies(
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
) -> list[list[ast.stmt]]:
    # Reject small fragments before allocating scopes or serializing syntax.
    bodies = _bodies(function)
    root = bodies[0][0] if isinstance(function, ast.Lambda) else function
    sizes: dict[ast.AST, tuple[int, int, int]] = {}
    for node in reversed(list(ast.walk(root))):
        children = [sizes[child] for child in ast.iter_child_nodes(node)]
        sizes[node] = (
            int(isinstance(node, (ast.stmt, ast.expr)))
            + sum(size for size, _, _ in children),
            int(isinstance(node, ast.stmt)) + sum(count for _, count, _ in children),
            int(isinstance(node, _OPERATIONS)) + sum(count for _, _, count in children),
        )
    return [
        body
        for body in bodies
        if sum(sizes[node][0] for node in body) >= MIN_CLONE_NODES
        and (
            sum(sizes[node][1] for node in body) >= MIN_CLONE_STATEMENTS
            or (
                len(body) == 1
                and sum(sizes[node][2] for node in body)
                >= MIN_SINGLE_STATEMENT_OPERATIONS
            )
        )
    ]


def duplicate_bodies(
    root: Path, parsed_sources: Mapping[Path, ast.Module]
) -> tuple[tuple[CloneSite, ...], ...]:
    """Report substantial bound-name-equivalent Python bodies and logic blocks.

    Digest matches are checked against full token equality. Nested reports already
    covered by a larger duplicate are suppressed, never the larger violation.
    """
    groups: dict[bytes, list[_Candidate]] = {}
    for path, tree in sorted(parsed_sources.items()):
        bindings: _Bindings | None = None
        for function in ast.walk(tree):
            if not isinstance(function, _FUNCTIONS):
                continue
            bodies = _substantial_bodies(function)
            if not bodies:
                continue
            if bindings is None:
                bindings = _Bindings(tree)
            seen: set[tuple[int, int, int, int]] = set()
            for body in bodies:
                site = CloneSite(
                    path.relative_to(root).as_posix(),
                    body[0].lineno,
                    body[-1].end_lineno or body[-1].lineno,
                    (
                        f"<lambda@{function.lineno}:{function.col_offset}>"
                        if isinstance(function, ast.Lambda)
                        else function.name
                    ),
                    body[0].col_offset,
                    body[-1].end_col_offset or 0,
                )
                span = (site.line, site.column, site.end_line, site.end_column)
                if span in seen:
                    continue
                seen.add(span)
                tokens, nodes, statements, operations = _tokens(
                    body, bindings, function
                )
                if nodes < MIN_CLONE_NODES or (
                    statements < MIN_CLONE_STATEMENTS
                    and not (
                        len(body) == 1 and operations >= MIN_SINGLE_STATEMENT_OPERATIONS
                    )
                ):
                    continue
                canonical = json.dumps(
                    tokens, ensure_ascii=True, separators=(",", ":")
                ).encode("ascii")
                digest = hashlib.sha256(canonical).digest()
                groups.setdefault(digest, []).append(_Candidate(site, canonical, nodes))
    reports: list[tuple[CloneSite, ...]] = []
    covered: dict[str, list[tuple[tuple[int, int], tuple[int, int]]]] = {}
    # Keep compact, unambiguously serialized tokens for exact collision checks.
    # File-wide lexical maps and Python token tuples are released after each file.
    for candidates in sorted(groups.values(), key=lambda group: -group[0].size):
        if len(candidates) < 2:
            continue
        exact: dict[bytes, list[CloneSite]] = {}
        for candidate in candidates:
            exact.setdefault(candidate.canonical, []).append(candidate.site)
        for sites in exact.values():
            if len(sites) < 2:
                continue
            if all(
                any(
                    first <= (site.line, site.column)
                    and last >= (site.end_line, site.end_column)
                    for first, last in covered.get(site.path, ())
                )
                for site in sites
            ):
                continue
            reports.append(tuple(sorted(sites)))
            for site in sites:
                covered.setdefault(site.path, []).append(
                    ((site.line, site.column), (site.end_line, site.end_column))
                )
    return tuple(sorted(reports))
