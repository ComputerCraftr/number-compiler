"""Iterative value adapters used by the comma right-congruence audit."""

from __future__ import annotations

from collections.abc import Callable, Hashable
from dataclasses import dataclass
from typing import TypeGuard

from number_compiler.sequences.comma.boundary_chart import BoundaryChart
from number_compiler.sequences.comma.boundary_quotient import BoundaryState


@dataclass(frozen=True, slots=True)
class _Visit:
    value: object


@dataclass(frozen=True, slots=True)
class _Assemble:
    is_tuple: bool
    child_count: int


@dataclass(frozen=True, slots=True)
class _Leave:
    identity: int


_ValueOperation = _Visit | _Assemble | _Leave


def is_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    return isinstance(value, tuple)


def _is_object_list(value: object) -> TypeGuard[list[object]]:
    return isinstance(value, list)


def _is_object_sequence(
    value: object,
) -> TypeGuard[tuple[object, ...] | list[object]]:
    return is_object_tuple(value) or _is_object_list(value)


def _map_nested(value: object, convert_leaf: Callable[[object], object]) -> object:
    """Map tuple/list leaves in postorder and reject recursive containers."""
    pending: list[_ValueOperation] = [_Visit(value)]
    converted: list[object] = []
    active_containers: set[int] = set()

    while pending:
        operation = pending.pop()
        if isinstance(operation, _Leave):
            active_containers.remove(operation.identity)
            continue
        if isinstance(operation, _Assemble):
            children = (
                converted[-operation.child_count :] if operation.child_count else []
            )
            if operation.child_count:
                del converted[-operation.child_count :]
            converted.append(tuple(children) if operation.is_tuple else children)
            continue

        current = operation.value
        if _is_object_sequence(current):
            identity = id(current)
            if identity in active_containers:
                raise ValueError("audit value contains a recursive container")
            active_containers.add(identity)
            pending.append(_Leave(identity))
            pending.append(_Assemble(is_object_tuple(current), len(current)))
            pending.extend(_Visit(child) for child in reversed(current))
        else:
            converted.append(convert_leaf(current))

    if len(converted) != 1:
        raise AssertionError("iterative value conversion left an invalid stack")
    return converted[0]


def state_record(state: Hashable) -> dict[str, object]:
    """Render a comma chart/state for a non-authoritative audit report."""
    if isinstance(state, BoundaryChart):
        return {
            "state_kind": "chart",
            "chart": state.kind,
            "leading": state.leading,
            "delta": state.delta,
            "coordinate": state.coordinate,
        }
    if isinstance(state, str):
        return {"state": state}
    return {"state": repr(state)}


def _report_leaf(value: object) -> object:
    if isinstance(value, (str, int, float, bool, type(None))):
        return value
    if isinstance(value, BoundaryChart):
        return state_record(value)
    return repr(value)


def json_report_value(value: object) -> object:
    """Normalize nested audit values while preserving tuple/list shape."""
    return _map_nested(value, _report_leaf)


def _stable_leaf(value: object) -> object:
    if isinstance(value, BoundaryChart):
        return (
            "chart",
            value.kind,
            value.leading,
            value.delta,
            value.coordinate,
        )
    if isinstance(value, BoundaryState):
        return ("boundary", value.kind, value.a, value.exponent_residue)
    return value


def stable_value(value: Hashable) -> Hashable:
    """Canonicalize nested hashable audit values without recursion."""
    converted = _map_nested(value, _stable_leaf)
    if not isinstance(converted, Hashable):
        raise TypeError("stable normalization produced an unhashable value")
    return converted
