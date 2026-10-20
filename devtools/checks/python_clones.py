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
from collections import deque
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import TypeGuard

from devtools.checks.clone_shapes import (
    CloneCandidate as _Candidate,
)
from devtools.checks.clone_shapes import (
    CloneSite,
    structural_shape_hashes,
)

MIN_CLONE_NODES = 24
MIN_CLONE_STATEMENTS = 3
MIN_SINGLE_STATEMENT_OPERATIONS = 3
OPERATIONS = (
    ast.BinOp,
    ast.UnaryOp,
    ast.BoolOp,
    ast.Compare,
    ast.IfExp,
    ast.comprehension,
)
FUNCTIONS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_IGNORED_FIELDS = frozenset({"annotation", "returns", "type_comment", "type_params"})
_STATEMENT_SUITE_FIELDS = frozenset({"body", "orelse", "finalbody"})
_BINDING_FIELDS: dict[type[ast.AST], str] = {
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
    bound: set[str] = field(default_factory=set[str])
    globals: set[str] = field(default_factory=set[str])
    nonlocals: set[str] = field(default_factory=set[str])


@dataclass(frozen=True, slots=True)
class _IdentifierValue:
    text: str | None
    binding: tuple[_Scope | None, str] | None


@dataclass(frozen=True, slots=True)
class IdentifierToken:
    prefix: str
    identifier: _IdentifierValue
    suffix: str


@dataclass(frozen=True, slots=True)
class _IdentifierLiteral:
    type_name: str
    identifier: _IdentifierValue


TokenBinding = tuple[_Scope | None, str]


@dataclass(frozen=True, slots=True)
class IdentifierReservation:
    binding: TokenBinding


_TokenEvent = str | IdentifierToken | IdentifierReservation


@dataclass(frozen=True, slots=True)
class _TokenFragment:
    events: tuple[_TokenEvent, ...]
    nodes: int
    statements: int
    operations: int


def _object_list(value: object) -> TypeGuard[list[object]]:
    return isinstance(value, list)


def _statement_list(value: object) -> TypeGuard[list[ast.stmt]]:
    return _object_list(value) and all(isinstance(item, ast.stmt) for item in value)


def _children(node: ast.AST) -> list[ast.AST]:
    children: list[ast.AST] = []
    for name, value in ast.iter_fields(node):
        if name in _IGNORED_FIELDS:
            continue
        if isinstance(value, ast.AST):
            children.append(value)
        elif _object_list(value):
            children.extend(item for item in value if isinstance(item, ast.AST))
    return children


def module_ast_inventory(
    root: ast.Module,
) -> tuple[
    list[ast.AST],
    dict[ast.AST, tuple[ast.AST, ...]],
    dict[ast.AST, tuple[ast.AST, ...]],
    dict[ast.AST, tuple[list[ast.stmt], ...]],
    dict[ast.stmt, tuple[ast.stmt, ...]],
]:
    """Collect child views and nested statement dependencies in one module walk."""
    nodes: list[ast.AST] = []
    all_children: dict[ast.AST, tuple[ast.AST, ...]] = {}
    lexical_children: dict[ast.AST, tuple[ast.AST, ...]] = {}
    statement_suites: dict[ast.AST, tuple[list[ast.stmt], ...]] = {}
    statement_children: dict[ast.stmt, list[ast.stmt]] = {}
    pending: deque[tuple[ast.AST, ast.stmt | None, bool]] = deque([(root, None, True)])
    while pending:
        node, enclosing_statement, serialized_path = pending.popleft()
        nodes.append(node)
        full: list[ast.AST] = []
        lexical: list[ast.AST] = []
        serialized: list[ast.AST] = []
        suites: list[list[ast.stmt]] = []
        for name, value in ast.iter_fields(node):
            children: tuple[ast.AST, ...]
            if isinstance(value, ast.AST):
                children = (value,)
            elif _object_list(value):
                if value and name in _STATEMENT_SUITE_FIELDS and _statement_list(value):
                    suites.append(value)
                children = tuple(child for child in value if isinstance(child, ast.AST))
            else:
                continue
            full.extend(children)
            if name not in _IGNORED_FIELDS:
                lexical.extend(children)
                serialized_children = children
                if (
                    name == "body"
                    and isinstance(node, (*FUNCTIONS, ast.ClassDef))
                    and serialized_children
                ):
                    first = serialized_children[0]
                    if (
                        isinstance(first, ast.Expr)
                        and isinstance(first.value, ast.Constant)
                        and isinstance(first.value.value, str)
                    ):
                        serialized_children = serialized_children[1:]
                if serialized_path:
                    serialized.extend(serialized_children)
        full_children = tuple(full)
        all_children[node] = full_children
        lexical_children[node] = tuple(lexical)
        if suites:
            statement_suites[node] = tuple(suites)
        current_statement = node if isinstance(node, ast.stmt) else enclosing_statement
        all_children_serialized = serialized_path and len(serialized) == len(
            full_children
        )
        serialized_set = (
            None if not serialized_path or all_children_serialized else set(serialized)
        )
        for child in full_children:
            child_is_serialized = serialized_path and (
                all_children_serialized
                or (serialized_set is not None and child in serialized_set)
            )
            if (
                child_is_serialized
                and isinstance(child, ast.stmt)
                and current_statement is not None
            ):
                statement_children.setdefault(current_statement, []).append(child)
            pending.append(
                (
                    child,
                    current_statement if child_is_serialized else enclosing_statement,
                    child_is_serialized,
                )
            )
    return (
        nodes,
        all_children,
        lexical_children,
        statement_suites,
        {node: tuple(children) for node, children in statement_children.items()},
    )


class Bindings:
    """Lexical owners and bindings for one source file and its nested scopes."""

    def __init__(
        self,
        root: ast.Module,
        *,
        lexical_children: Mapping[ast.AST, Sequence[ast.AST]] | None = None,
    ) -> None:
        self.owner: dict[ast.AST, _Scope] = {}
        self.inner: dict[ast.AST, _Scope] = {}
        self._resolved: dict[tuple[ast.AST, str], tuple[_Scope | None, str]] = {}
        outer = _Scope(None, "external")
        pending: list[tuple[ast.AST, _Scope]] = [(root, outer)]
        while pending:
            node, scope = pending.pop()
            self.owner[node] = scope
            node_children = (
                _children(node) if lexical_children is None else lexical_children[node]
            )
            children = [(child, scope) for child in node_children]
            if isinstance(node, (*FUNCTIONS, ast.ClassDef, *_COMPREHENSIONS)):
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
                if isinstance(node, FUNCTIONS):
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
            if not isinstance(function, FUNCTIONS):
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
        key = (node, name)
        cached = self._resolved.get(key)
        if cached is not None:
            return cached
        start = self.owner[node]
        scope: _Scope | None = start
        result: tuple[_Scope | None, str]
        while scope is not None:
            if name in scope.globals:
                result = (None, name)
                self._resolved[key] = result
                return result
            if name in scope.bound and name not in scope.nonlocals:
                if scope.kind in {"external", "class"}:
                    result = (None, name)
                else:
                    result = (scope, name)
                self._resolved[key] = result
                return result
            scope = scope.parent
            # Methods/closures do not capture class namespace attributes.
            if scope is not None and scope.kind == "class" and start.kind != "class":
                scope = scope.parent
        result = (None, name)
        self._resolved[key] = result
        return result


def _without_docstring(body: Sequence[ast.stmt]) -> list[ast.stmt]:
    if body and isinstance(body[0], ast.Expr):
        value = body[0].value
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return list(body[1:])
    return list(body)


def _identifier_value(
    node: ast.AST,
    name: str,
    bindings: Bindings,
    scope: _Scope,
    captures: Mapping[_Scope, int],
) -> _IdentifierValue:
    binding = bindings.resolve(node, name)
    if binding[0] is scope and binding in bindings.parameters:
        return _IdentifierValue(f"parameter:{bindings.parameters[binding]}", None)
    if binding[0] is not None and binding[0] in captures:
        prefix = f"capture:{captures[binding[0]]}:"
        if binding in bindings.parameters:
            return _IdentifierValue(
                prefix + f"parameter:{bindings.parameters[binding]}", None
            )
        return _IdentifierValue(
            prefix + f"local:{bindings.local_positions[binding]}", None
        )
    if binding[0] is not None:
        return _IdentifierValue(None, binding)
    return _IdentifierValue(f"free:{name!r}", None)


def function_tokens(
    body: Sequence[ast.stmt],
    bindings: Bindings,
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
) -> tuple[tuple[str, ...], int, int, int]:
    fragment = _token_fragment(
        body, _TokenContext(bindings, function), include_body_list=True
    )
    names: dict[TokenBinding, int] = {}
    tokens: list[str] = []
    consume_token_events(fragment.events, names, tokens)
    return tuple(tokens), fragment.nodes, fragment.statements, fragment.operations


class _TokenContext:
    """Binding classification shared by one function's token projections."""

    def __init__(
        self,
        bindings: Bindings,
        function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
    ) -> None:
        self.bindings = bindings
        self.scope = bindings.inner[function]
        captures: dict[_Scope, int] = {}
        parent, depth = self.scope.parent, 0
        while parent is not None:
            if parent.kind in {"function", "comprehension"}:
                depth += 1
                captures[parent] = depth
            parent = parent.parent
        self.captures = captures

    def identifier(self, node: ast.AST, name: str) -> _IdentifierValue:
        return _identifier_value(node, name, self.bindings, self.scope, self.captures)


def _scalar_identifier_token(
    type_name: str, identifier: _IdentifierValue
) -> str | IdentifierToken:
    if identifier.binding is not None:
        # Generated local IDs contain only ASCII letters, colon and digits, so
        # repr always uses the same single-quote delimiters as the reference.
        return IdentifierToken(f"{type_name}:'", identifier, "'")
    if identifier.text is None:
        raise AssertionError("fixed identifier has no token text")
    return f"{type_name}:{identifier.text!r}"


def _token_fragment(
    body: Sequence[ast.stmt],
    context: _TokenContext,
    *,
    include_body_list: bool,
    statement_fragments: Mapping[ast.stmt, _TokenFragment] | None = None,
) -> _TokenFragment:
    events: list[_TokenEvent] = []
    pending: list[object] = [list(body)] if include_body_list else list(reversed(body))
    nodes = statements = operations = 0
    while pending:
        value = pending.pop()
        if isinstance(value, ast.stmt) and statement_fragments is not None:
            child_fragment = statement_fragments.get(value)
            if child_fragment is not None:
                events.extend(child_fragment.events)
                nodes += child_fragment.nodes
                statements += child_fragment.statements
                operations += child_fragment.operations
                continue
        if isinstance(value, ast.Name):
            nodes += 1
            events.append(
                IdentifierToken(
                    "Name:",
                    context.identifier(value, value.id),
                    f":{type(value.ctx).__name__}",
                )
            )
            continue
        if isinstance(value, ast.Constant):
            nodes += 1
            events.append(
                f"Constant:{type(value.value).__name__}:{value.value!r}:{value.kind!r}"
            )
            continue
        if isinstance(value, _IdentifierLiteral):
            events.append(_scalar_identifier_token(value.type_name, value.identifier))
        elif isinstance(value, ast.AST):
            nodes += isinstance(value, (ast.stmt, ast.expr))
            operations += isinstance(value, OPERATIONS)
            statements += isinstance(value, ast.stmt) and not isinstance(
                value, ast.Pass
            )
            events.append(type(value).__name__)
            fields: list[object] = []
            reservations: list[IdentifierReservation] = []
            binding_field = _BINDING_FIELDS.get(type(value))
            for name, item in ast.iter_fields(value):
                if name in _IGNORED_FIELDS:
                    continue
                if isinstance(value, ast.alias) and name == "asname":
                    item = value.asname or value.name.split(".")[0]
                if name == binding_field and isinstance(item, str):
                    identifier = context.identifier(value, item)
                    if identifier.binding is not None:
                        reservations.append(IdentifierReservation(identifier.binding))
                    item = _IdentifierLiteral(type(item).__name__, identifier)
                if isinstance(value, ast.Nonlocal) and name == "names":
                    identifiers = [
                        context.identifier(value, identifier)
                        for identifier in value.names
                    ]
                    reservations.extend(
                        IdentifierReservation(identifier.binding)
                        for identifier in identifiers
                        if identifier.binding is not None
                    )
                    item = [
                        _IdentifierLiteral("str", identifier)
                        for identifier in identifiers
                    ]
                if (
                    name == "body"
                    and _object_list(item)
                    and isinstance(
                        value, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
                    )
                ):
                    item = _without_docstring(value.body)
                fields.append(item)
            # The reference walk resolves binding fields eagerly while reading
            # an AST node, before serializing any of that node's children.
            events.extend(reservations)
            pending.extend(reversed(fields))
        elif _object_list(value):
            events.append(f"list:{len(value)}")
            pending.extend(reversed(value))
        else:
            events.append(f"{type(value).__name__}:{value!r}")
    return _TokenFragment(tuple(events), nodes, statements, operations)


def _render_token_event(event: IdentifierToken, names: dict[TokenBinding, int]) -> str:
    identifier = event.identifier
    if identifier.binding is not None:
        text = f"local:{names.setdefault(identifier.binding, len(names))}"
    elif identifier.text is not None:
        text = identifier.text
    else:
        raise AssertionError("identifier token has no value")
    return event.prefix + text + event.suffix


def consume_token_events(
    events: Sequence[_TokenEvent],
    names: dict[TokenBinding, int],
    tokens: list[str],
) -> None:
    """Consume a fragment in one loop, avoiding a call for every raw token."""
    for event in events:
        if isinstance(event, str):
            tokens.append(event)
        elif isinstance(event, IdentifierReservation):
            names.setdefault(event.binding, len(names))
        else:
            tokens.append(_render_token_event(event, names))


class FunctionTokenProjection:
    """Cache raw statement events and alpha-renumber them per candidate body."""

    def __init__(
        self,
        bindings: Bindings,
        function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
        statement_children: Mapping[ast.stmt, Sequence[ast.stmt]] | None = None,
    ) -> None:
        self.context = _TokenContext(bindings, function)
        self.fragments: dict[ast.stmt, _TokenFragment] = {}
        self.statement_children = statement_children or {}

    def _fragment(self, root: ast.stmt) -> _TokenFragment:
        """Build statement fragments bottom-up without recursive Python calls."""
        existing = self.fragments.get(root)
        if existing is not None:
            return existing
        pending: list[tuple[ast.stmt, bool]] = [(root, False)]
        scheduled = {root}
        while pending:
            statement, expanded = pending.pop()
            if statement in self.fragments:
                continue
            if expanded:
                self.fragments[statement] = _token_fragment(
                    (statement,),
                    self.context,
                    include_body_list=False,
                    statement_fragments=self.fragments,
                )
                continue
            pending.append((statement, True))
            for child in reversed(self.statement_children.get(statement, ())):
                if child not in self.fragments and child not in scheduled:
                    scheduled.add(child)
                    pending.append((child, False))
        return self.fragments[root]

    def tokenize(
        self, body: Sequence[ast.stmt]
    ) -> tuple[tuple[str, ...], int, int, int]:
        names: dict[TokenBinding, int] = {}
        tokens = [f"list:{len(body)}"]
        nodes = statements = operations = 0
        for statement in body:
            fragment = self._fragment(statement)
            consume_token_events(fragment.events, names, tokens)
            nodes += fragment.nodes
            statements += fragment.statements
            operations += fragment.operations
        return tuple(tokens), nodes, statements, operations


def _window_bodies(body: Sequence[ast.stmt]) -> Iterator[list[ast.stmt]]:
    for index in range(len(body) - MIN_CLONE_STATEMENTS + 1):
        yield list(body[index : index + MIN_CLONE_STATEMENTS])


def _may_contain_substantial_window(
    body: Sequence[ast.stmt],
    subtree_sizes: Mapping[ast.AST, tuple[int, int, int]],
) -> bool:
    # These subtree counts are upper bounds on the serialized token counts
    # (they include fields/docstrings ignored by tokens). If even the complete
    # suite is too small, none of its windows can meet the same lower bounds.
    return (
        sum(subtree_sizes[node][0] for node in body) >= MIN_CLONE_NODES
        and sum(subtree_sizes[node][1] for node in body) >= MIN_CLONE_STATEMENTS
    )


def _bodies(
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
    subtree_sizes: Mapping[ast.AST, tuple[int, int, int]],
    *,
    lexical_children: Mapping[ast.AST, Sequence[ast.AST]] | None = None,
    statement_suites: Mapping[ast.AST, Sequence[list[ast.stmt]]] | None = None,
) -> Iterator[Sequence[ast.stmt]]:
    """Stream complete suites and viable fixed windows, never interval pairs."""
    if isinstance(function, ast.Lambda):
        # Reuse the original expression nodes and lexical owners. Only the
        # implicit return is synthetic, allowing comparison with def bodies.
        yield [ast.copy_location(ast.Return(value=function.body), function.body)]
        return
    pending: list[ast.AST] = [function]
    while pending:
        node = pending.pop()
        if node is not function and isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
        ):
            continue  # These have their own function inventory.
        suites: Sequence[list[ast.stmt]]
        if statement_suites is None:
            suites = tuple(
                value
                for _name, value in ast.iter_fields(node)
                if _statement_list(value) and value
            )
        else:
            suites = statement_suites.get(node, ())
        for value in suites:
            body = _without_docstring(value) if node is function else value
            if body:
                yield body
            if len(body) > MIN_CLONE_STATEMENTS and _may_contain_substantial_window(
                body, subtree_sizes
            ):
                yield from _window_bodies(body)
        node_children = (
            _children(node) if lexical_children is None else lexical_children[node]
        )
        pending.extend(reversed(node_children))


def substantial_bodies(
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
    subtree_sizes: Mapping[ast.AST, tuple[int, int, int]],
    *,
    lexical_children: Mapping[ast.AST, Sequence[ast.AST]] | None = None,
    statement_suites: Mapping[ast.AST, Sequence[list[ast.stmt]]] | None = None,
) -> Iterator[Sequence[ast.stmt]]:
    # Reject small fragments before allocating scopes or serializing syntax.
    if isinstance(function, ast.Lambda):
        expression_size = subtree_sizes[function.body]
        size = expression_size[0] + 1
        statements = expression_size[1] + 1
        operations = expression_size[2]
        if size >= MIN_CLONE_NODES and (
            statements >= MIN_CLONE_STATEMENTS
            or operations >= MIN_SINGLE_STATEMENT_OPERATIONS
        ):
            yield from _bodies(
                function,
                subtree_sizes,
                lexical_children=lexical_children,
                statement_suites=statement_suites,
            )
        return
    for body in _bodies(
        function,
        subtree_sizes,
        lexical_children=lexical_children,
        statement_suites=statement_suites,
    ):
        if sum(subtree_sizes[node][0] for node in body) < MIN_CLONE_NODES:
            continue
        if sum(subtree_sizes[node][1] for node in body) >= MIN_CLONE_STATEMENTS or (
            len(body) == 1
            and sum(subtree_sizes[node][2] for node in body)
            >= MIN_SINGLE_STATEMENT_OPERATIONS
        ):
            yield body


def canonical_tokens(tokens: Sequence[str]) -> bytes:
    return json.dumps(tokens, ensure_ascii=True, separators=(",", ":")).encode("ascii")


def _canonical_candidate(
    candidate: _Candidate, collision_bindings: dict[ast.Module, Bindings]
) -> bytes:
    if candidate.function is None or candidate.tree is None:
        raise AssertionError("singleton candidate lost its AST locator")
    bindings = collision_bindings.get(candidate.tree)
    if bindings is None:
        bindings = Bindings(candidate.tree)
        collision_bindings[candidate.tree] = bindings
    tokens, _nodes, _statements, _operations = function_tokens(
        candidate.body, bindings, candidate.function
    )
    return canonical_tokens(tokens)


def duplicate_bodies(
    root: Path,
    parsed_sources: Mapping[Path, ast.Module],
    *,
    profile_callback: Callable[[Mapping[str, int]], None] | None = None,
) -> tuple[tuple[CloneSite, ...], ...]:
    """Report substantial bound-name-equivalent Python bodies and logic blocks.

    Digest matches are checked against full token equality. Nested reports already
    covered by a larger duplicate are suppressed, never the larger violation.
    """
    shape_groups: dict[tuple[int, ...], list[_Candidate]] = {}
    groups: dict[bytes, list[_Candidate]] = {}
    collision_bindings: dict[ast.Module, Bindings] = {}
    profile_counts = (
        {
            "modules": 0,
            "ast_nodes": 0,
            "functions": 0,
            "candidate_bodies": 0,
            "tokenized_bodies": 0,
            "eligible_bodies": 0,
            "digest_matches": 0,
        }
        if profile_callback is not None
        else None
    )
    for module_number, (path, tree) in enumerate(
        sorted(parsed_sources.items()), start=1
    ):
        relative_path = path.relative_to(root).as_posix()
        (
            nodes,
            all_children,
            lexical_children,
            statement_suites,
            _statement_children,
        ) = module_ast_inventory(tree)
        if profile_counts is not None:
            profile_counts["modules"] = module_number
            profile_counts["ast_nodes"] += len(nodes)
        subtree_sizes: dict[ast.AST, tuple[int, int, int]] = {}
        for node in reversed(nodes):
            children = [subtree_sizes[child] for child in all_children[node]]
            subtree_sizes[node] = (
                int(isinstance(node, (ast.stmt, ast.expr)))
                + sum(size for size, _, _ in children),
                int(isinstance(node, ast.stmt))
                + sum(count for _, count, _ in children),
                int(isinstance(node, OPERATIONS))
                + sum(count for _, _, count in children),
            )
        del all_children
        node_shapes: dict[ast.AST, int] | None = None
        for function in nodes:
            if not isinstance(function, FUNCTIONS):
                continue
            if profile_counts is not None:
                profile_counts["functions"] += 1
            seen: set[tuple[int, int, int, int]] = set()
            for body in substantial_bodies(
                function,
                subtree_sizes,
                lexical_children=lexical_children,
                statement_suites=statement_suites,
            ):
                if profile_counts is not None:
                    profile_counts["candidate_bodies"] += 1
                site = CloneSite(
                    relative_path,
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
                if node_shapes is None:
                    node_shapes = structural_shape_hashes(
                        nodes,
                        ignored_fields=_IGNORED_FIELDS,
                        binding_fields=_BINDING_FIELDS,
                    )
                shape = (
                    (hash(("Return", "value", ("child", node_shapes[function.body]))),)
                    if isinstance(function, ast.Lambda)
                    else tuple(node_shapes[node] for node in body)
                )
                shape_groups.setdefault(shape, []).append(
                    _Candidate(site, None, 0, body, function, tree)
                )
        if (
            profile_callback is not None
            and profile_counts is not None
            and module_number % 50 == 0
        ):
            profile_callback(dict(profile_counts))
    shared_shapes: dict[ast.Module, list[_Candidate]] = {}
    for candidates in shape_groups.values():
        if len(candidates) > 1:
            for candidate in candidates:
                assert candidate.tree is not None
                shared_shapes.setdefault(candidate.tree, []).append(candidate)
    del shape_groups
    if profile_counts is not None and profile_callback is not None:
        profile_counts["shared_shape_modules"] = len(shared_shapes)
        profile_counts["shared_shape_candidates"] = sum(
            len(candidates) for candidates in shared_shapes.values()
        )
        profile_callback(dict(profile_counts))
    for tree, candidates in shared_shapes.items():
        (
            _nodes,
            _all_children,
            lexical_children,
            _statement_suites,
            statement_children,
        ) = module_ast_inventory(tree)
        bindings = Bindings(tree, lexical_children=lexical_children)
        projections: dict[ast.AST, FunctionTokenProjection] = {}
        for candidate in candidates:
            candidate_function = candidate.function
            if candidate_function is None:
                raise AssertionError("coarse clone candidate lost its function")
            projection = projections.get(candidate_function)
            if projection is None:
                projection = FunctionTokenProjection(
                    bindings, candidate_function, statement_children
                )
                projections[candidate_function] = projection
            tokens, node_count, statements, operations = projection.tokenize(
                candidate.body
            )
            if profile_counts is not None:
                profile_counts["tokenized_bodies"] += 1
            if node_count < MIN_CLONE_NODES or (
                statements < MIN_CLONE_STATEMENTS
                and not (
                    len(candidate.body) == 1
                    and operations >= MIN_SINGLE_STATEMENT_OPERATIONS
                )
            ):
                continue
            if profile_counts is not None:
                profile_counts["eligible_bodies"] += 1
            candidate.size = node_count
            canonical = canonical_tokens(tokens)
            digest = hashlib.sha256(canonical).digest()
            exact_candidates = groups.get(digest)
            if exact_candidates is None:
                groups[digest] = [candidate]
            else:
                if profile_counts is not None:
                    profile_counts["digest_matches"] += 1
                collision_bindings.setdefault(tree, bindings)
                if len(exact_candidates) == 1 and exact_candidates[0].canonical is None:
                    first = exact_candidates[0]
                    first.canonical = _canonical_candidate(first, collision_bindings)
                    first.body = ()
                    first.function = None
                    first.tree = None
                candidate.canonical = canonical
                exact_candidates.append(candidate)
            del tokens
    reports: list[tuple[CloneSite, ...]] = []
    covered: dict[str, list[tuple[tuple[int, int], tuple[int, int]]]] = {}
    # Keep compact, unambiguously serialized tokens for exact collision checks.
    # Projections are function-local. Singleton AST locators and collision-only
    # lexical maps remain invocation-local until exact grouping completes.
    for candidates in sorted(groups.values(), key=lambda group: -group[0].size):
        if len(candidates) < 2:
            continue
        exact: dict[bytes, list[CloneSite]] = {}
        for candidate in candidates:
            if candidate.canonical is None:
                raise AssertionError("digest singleton entered a collision group")
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
    result = tuple(sorted(reports))
    if profile_callback is not None and profile_counts is not None:
        profile_counts["duplicate_groups"] = len(result)
        profile_counts["duplicate_sites"] = sum(len(group) for group in result)
        profile_callback(dict(profile_counts))
    return result
