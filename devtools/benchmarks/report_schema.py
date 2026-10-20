"""Validate record shapes at developer-report serialization boundaries."""

from collections.abc import Mapping, Sequence
from typing import cast


def record(value: object) -> dict[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError("report component must be a record")
    source = cast(Mapping[object, object], value)
    result: dict[str, object] = {}
    for key, item in source.items():
        if not isinstance(key, str):
            raise TypeError("report field names must be strings")
        result[key] = item
    return result


def sequence(value: object) -> tuple[object, ...]:
    if not isinstance(value, (list, tuple)):
        raise TypeError("report component must be a sequence")
    source = cast(Sequence[object], value)
    items: list[object] = []
    items.extend(source)
    return tuple(items)


def records(value: object) -> tuple[dict[str, object], ...]:
    return tuple(record(item) for item in sequence(value))
