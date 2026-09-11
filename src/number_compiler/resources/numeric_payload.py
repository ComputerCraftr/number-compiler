"""Structural checks for numeric words split across otherwise bounded limbs.

This is a conservative representation check, not a provenance oracle.  Known,
validated semantic records are boundaries; untyped numeric storage is examined
as a connected aggregate, including nested containers and arbitrary records.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, fields, is_dataclass
from types import GeneratorType

from number_compiler.arithmetic.contracts.scoped_handles import CarryBit, WordLimb
from number_compiler.resources.payload_containers import audit_mapping_items


@dataclass(frozen=True, slots=True)
class NumericAggregateAudit:
    forbidden_objects: frozenset[int]
    maximum_untyped_bits: int


def numeric_aggregate_audit(
    root: object, *, semantic: Callable[[object], bool]
) -> NumericAggregateAudit:
    """Find numeric aggregates wider than one limb without flattening their value.

    Numeric dictionary values join across scalar keys.  Interners with structured
    semantic keys instead contain independent records; their individual keys and
    values are still visited.  Neither field names nor ``WordLimb`` wrappers grant
    an exemption.  A shared child contributes once per stored edge, so repeating
    one limb four times does not evade the aggregate-width test.
    """
    widths: dict[int, int] = {}
    children: dict[int, tuple[object, ...]] = {}
    semantic_nodes: set[int] = set()
    visiting: set[int] = set()
    forbidden: set[int] = set()
    stack: list[tuple[object, bool]] = [(root, False)]
    maximum = 0
    while stack:
        value, finishing = stack.pop()
        identity = id(value)
        if identity in widths:
            continue
        if semantic(value) or value is None or isinstance(value, (str, bool)):
            widths[identity] = 0
            if semantic(value):
                semantic_nodes.add(identity)
            continue
        if type(value) is int:
            widths[identity] = max(1, abs(value).bit_length())
            continue
        if isinstance(value, (WordLimb, CarryBit)):
            widths[identity] = value.bits if isinstance(value, WordLimb) else 1
            continue
        if isinstance(value, (bytes, bytearray)):
            widths[identity] = len(value) * 8
            if widths[identity] > 64:
                forbidden.add(identity)
            maximum = max(maximum, widths[identity])
            continue
        if not finishing:
            if identity in visiting:
                # A cyclic untyped payload has no finite word decomposition.
                forbidden.add(identity)
                widths[identity] = 65
                continue
            visiting.add(identity)
            if isinstance(value, GeneratorType):
                frame = value.gi_frame
                parts = () if frame is None else tuple(frame.f_locals.values())
            elif isinstance(value, Mapping):
                parts = tuple(
                    item for pair in audit_mapping_items(value) for item in pair
                )
            elif isinstance(value, (Sequence, set, frozenset)):
                parts = tuple(value)
            elif is_dataclass(value) and not isinstance(value, type):
                parts = tuple(getattr(value, item.name) for item in fields(value))
            elif hasattr(value, "__dict__"):
                parts = tuple(vars(value).values())
            else:
                parts = tuple(
                    getattr(value, slot)
                    for slot in getattr(type(value), "__slots__", ())
                    if isinstance(slot, str) and hasattr(value, slot)
                )
            children[identity] = parts
            stack.append((value, True))
            stack.extend((child, False) for child in reversed(parts))
            continue
        parts = children[identity]
        if isinstance(value, Mapping):
            items = audit_mapping_items(value)
            keys, values = (
                tuple(key for key, _ in items),
                tuple(item for _, item in items),
            )
            key_width = sum(widths.get(id(key), 0) for key in keys)
            # Canonical dense local IDs are indexing metadata, only when the
            # descriptions they index have verified semantic types.
            dense_ids = (
                all(id(key) in semantic_nodes for key in keys)
                and all(type(item) is int for item in values)
                and set(values) == set(range(len(values)))
            )
            value_width = (
                0 if dense_ids else sum(widths.get(id(item), 0) for item in values)
            )
            width = max(key_width, value_width)
        else:
            width = sum(widths.get(id(child), 0) for child in parts)
        maximum = max(maximum, width)
        if width > 64:
            forbidden.add(identity)
        widths[identity] = width
        visiting.discard(identity)
    return NumericAggregateAudit(frozenset(forbidden), maximum)
