"""Closed, recursively checked field schemas for semantic payload boundaries."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import fields, is_dataclass
from types import UnionType
from typing import Literal, Union, cast, get_args, get_origin, get_type_hints

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle


def valid_semantic_record(
    root: object,
    *,
    geometry: Mapping[type[object], frozenset[str]],
    opaque: tuple[type[object], ...],
    states: tuple[type[object], ...],
    identity_bound: int,
    state_bound: int,
    pair_bound: int,
    radix_bound: int,
    source_handle_valid: Callable[[ArenaHandle], bool],
    resolved_hints: dict[type[object], dict[str, object]] | None = None,
) -> bool:
    """Validate every nested field; a familiar class alone grants no exemption."""
    pending: list[tuple[object, object, type[object] | None, str]] = [
        (root, type(root), None, "")
    ]
    visited: set[tuple[int, object]] = set()
    hints = {} if resolved_hints is None else resolved_hints
    identity_names = frozenset(
        (
            "left",
            "right",
            "before",
            "offset",
            "operator",
            "source",
            "first",
            "second",
            "low",
            "high",
            "view",
            "state",
            "local_id",
        )
    )
    while pending:
        value, expected, parent, name = pending.pop()
        if (
            expected is ArenaHandle
            and type(value) is ArenaHandle
            and value.kind == "source-tile"
        ):
            # Source tile IDs belong to a weak shared geometry interner, so
            # their numeric value is not bounded by this index's node count.
            # Membership in its actual source arena is the relevant proof.
            if not source_handle_valid(value):
                return False
            continue
        origin = get_origin(expected)
        arguments = cast(tuple[object, ...], get_args(expected))
        if origin in (UnionType, Union):
            selected: object | None = None
            for choice in arguments:
                if choice is type(None) and value is None:
                    selected = choice
                    break
                if isinstance(choice, type) and type(value) is choice:
                    selected = choice
                    break
                if (
                    isinstance(choice, type)
                    and choice.__name__ == "BlockEffect"
                    and type(value) in opaque
                ):
                    selected = choice
                    break
            if selected is None:
                return False
            pending.append((value, selected, parent, name))
            continue
        if origin is Literal:
            if not any(
                type(value) is type(item) and value == item for item in arguments
            ):
                return False
            continue
        if expected is type(None):
            if value is not None:
                return False
            continue
        if expected is int:
            if type(value) is not int:
                return False
            metadata = parent is not None and name in geometry.get(parent, frozenset())
            if metadata:
                if name in identity_names and not -1 <= value <= identity_bound:
                    return False
            else:
                bound = state_bound
                if name == "carry":
                    bound = 1
                elif name == "exit_carry":
                    bound = 2
                elif name == "growth":
                    bound = 1
                elif name == "previous_pair":
                    bound = pair_bound
                elif name in ("multiplier", "offset", "radix"):
                    bound = radix_bound
                elif name == "lower_mantissa":
                    bound = (1 << 31) - 1
                if not -1 <= value <= bound:
                    return False
            continue
        if expected is bool:
            if type(value) is not bool:
                return False
            continue
        if expected is str:
            if type(value) is not str:
                return False
            if parent is not None and name == "kind":
                domains = {
                    "_Program": ("identity", "compose", "shift", "mul3"),
                    "_ResultKey": ("events", "physical"),
                    "ArenaHandle": ("source", "source-tile"),
                    "ActionProgramID": (
                        "program",
                        "action-program",
                        "radix-division",
                        "reverse-program",
                    ),
                    "TransferSummaryID": (
                        "finite-port-function",
                        "radix-range-transfer",
                        "carry-interval-effect",
                        "collatz-range-effect",
                    ),
                }
                allowed = domains.get(parent.__name__)
                if allowed is not None and value not in allowed:
                    return False
            continue
        if expected is object:
            if type(value) is int and 0 <= value <= state_bound:
                continue
            if type(value) not in states:
                return False
            pending.append((value, type(value), parent, name))
            continue
        if origin is tuple:
            if type(value) is not tuple:
                return False
            children = cast(tuple[object, ...], value)
            if len(arguments) == 2 and arguments[1] is Ellipsis:
                pending.extend(
                    (child, arguments[0], parent, name) for child in children
                )
            elif len(arguments) == len(children):
                pending.extend(
                    (child, annotation, parent, name)
                    for child, annotation in zip(children, arguments, strict=True)
                )
            else:
                return False
            continue
        if isinstance(expected, type) and expected.__name__ == "BlockEffect":
            if type(value) not in opaque:
                return False
            continue
        if not isinstance(expected, type) or type(value) is not expected:
            return False
        if expected in opaque:
            continue
        if expected not in geometry:
            return False
        if not is_dataclass(value) or isinstance(value, type):
            return False
        identity = id(value), expected
        if identity in visited:
            continue
        visited.add(identity)
        if expected not in hints:
            hints[expected] = get_type_hints(expected)
        pending.extend(
            (
                getattr(value, field.name),
                hints[expected][field.name],
                expected,
                field.name,
            )
            for field in fields(value)
        )
    return True


__all__ = ["valid_semantic_record"]
