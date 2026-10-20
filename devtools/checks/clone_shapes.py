"""Cheap structural prefilters for exact binding-aware clone comparison."""

from __future__ import annotations

import ast
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import cast


@dataclass(frozen=True, order=True)
class CloneSite:
    path: str
    line: int
    end_line: int
    function: str
    column: int = 0
    end_column: int = 0


@dataclass
class CloneCandidate:
    site: CloneSite
    canonical: bytes | None
    size: int
    body: Sequence[ast.stmt] = ()
    function: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda | None = None
    tree: ast.Module | None = None


def _leading_docstring(values: list[object]) -> bool:
    if not values or not isinstance(values[0], ast.Expr):
        return False
    expression = values[0].value
    return isinstance(expression, ast.Constant) and type(expression.value) is str


def structural_shape_hashes(
    nodes: Sequence[ast.AST],
    *,
    ignored_fields: frozenset[str],
    binding_fields: Mapping[type[ast.AST], str],
) -> dict[ast.AST, int]:
    """Hash AST shape while erasing only names normalized by clone comparison.

    Equal canonical clone tokens always produce equal shape hashes. Hash
    collisions only admit extra exact comparisons; the clone decision still
    checks the complete binding-aware token stream.
    """
    hashes: dict[ast.AST, int] = {}
    for node in reversed(nodes):
        if isinstance(node, ast.Name):
            signature: tuple[object, ...] = ("Name", type(node.ctx).__name__)
        elif isinstance(node, ast.Constant):
            signature = (
                "Constant",
                type(node.value).__name__,
                repr(node.value),
                repr(node.kind),
            )
        else:
            parts: list[object] = [type(node).__name__]
            for field_name, raw_value in ast.iter_fields(node):
                value: object = cast(object, raw_value)
                if field_name in ignored_fields:
                    continue
                if isinstance(node, ast.alias) and field_name == "asname":
                    value = node.asname or node.name.split(".")[0]
                if field_name == binding_fields.get(type(node)) and isinstance(
                    value, str
                ):
                    parts.append((field_name, "identifier", type(value).__name__))
                    continue
                if isinstance(node, ast.Nonlocal) and field_name == "names":
                    names = cast(list[object], value)
                    parts.append((field_name, "identifiers", len(names)))
                    continue
                if (
                    field_name == "body"
                    and isinstance(
                        node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
                    )
                    and isinstance(value, list)
                    and _leading_docstring(cast(list[object], value))
                ):
                    value = cast(list[object], value)[1:]
                parts.append(field_name)
                if isinstance(value, ast.AST):
                    parts.append(("child", hashes[value]))
                elif isinstance(value, list):
                    items = cast(list[object], value)
                    parts.append(("list", len(items)))
                    for item in items:
                        if isinstance(item, ast.AST):
                            parts.append(("child", hashes[item]))
                        else:
                            parts.append(("value", type(item).__name__, repr(item)))
                else:
                    parts.append(("value", type(value).__name__, repr(value)))
            signature = tuple(parts)
        hashes[node] = hash(signature)
    return hashes


__all__ = ["CloneCandidate", "CloneSite", "structural_shape_hashes"]
