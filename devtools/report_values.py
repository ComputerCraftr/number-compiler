"""Typed container admission for untrusted developer reports and evidence."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TypeGuard


def _object_dictionary(value: object) -> TypeGuard[dict[object, object]]:
    """Narrow only the container, leaving every external key/value untrusted."""
    return isinstance(value, dict)


def object_list(value: object) -> TypeGuard[list[object]]:
    """Narrow a decoded JSON array without trusting its element types."""
    return type(value) is list


def string_keyed_mapping(value: object) -> Mapping[str, object] | None:
    """Validate JSON object keys before exposing a typed read-only mapping."""
    if not _object_dictionary(value):
        return None
    result: dict[str, object] = {}
    for raw_key, raw_item in value.items():
        if not isinstance(raw_key, str):
            return None
        item: object = raw_item
        result[raw_key] = item
    return result
