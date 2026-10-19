"""Validate record shapes at developer-report serialization boundaries."""

from collections.abc import Mapping


def record(value: object) -> dict[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError("report component must be a record")
    result: dict[str, object] = {}
    for raw_key, raw_item in value.items():
        key: object = raw_key
        item: object = raw_item
        if not isinstance(key, str):
            raise TypeError("report field names must be strings")
        result[key] = item
    return result


def sequence(value: object) -> tuple[object, ...]:
    if not isinstance(value, (list, tuple)):
        raise TypeError("report component must be a sequence")
    items: list[object] = []
    for raw_item in value:
        item: object = raw_item
        items.append(item)
    return tuple(items)


def records(value: object) -> tuple[dict[str, object], ...]:
    return tuple(record(item) for item in sequence(value))
