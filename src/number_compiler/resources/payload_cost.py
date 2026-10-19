"""Shared iterative retained-payload charging for immutable observation trees."""

from __future__ import annotations

from dataclasses import fields, is_dataclass
from typing import TypeGuard


def _payload_sequence(value: object) -> TypeGuard[tuple[object, ...] | list[object]]:
    return isinstance(value, (tuple, list))


def retained_payload_node_count(value: object) -> int:
    """Count retained tuple/dataclass slots and scalar payloads iteratively."""
    pending = [value]
    count = 0
    while pending:
        current = pending.pop()
        if type(current) is int:
            count += max(1, (current.bit_length() + 63) // 64)
        elif type(current) is str:
            count += max(1, (len(current.encode("utf-8")) + 7) // 8)
        else:
            count += 1
        if _payload_sequence(current):
            count += len(current)
            pending.extend(current)
        elif is_dataclass(current) and not isinstance(current, type):
            attributes = fields(current)
            count += len(attributes)
            pending.extend(getattr(current, attribute.name) for attribute in attributes)
    return count
