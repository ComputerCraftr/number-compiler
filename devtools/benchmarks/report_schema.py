"""Validate record shapes at developer-report serialization boundaries."""

from collections.abc import Mapping


def record(value: object) -> dict[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError("report component must be a record")
    result: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise TypeError("report field names must be strings")
        result[key] = item
    return result


def sequence(value: object) -> tuple[object, ...]:
    if not isinstance(value, (list, tuple)):
        raise TypeError("report component must be a sequence")
    return tuple(value)


def records(value: object) -> tuple[dict[str, object], ...]:
    return tuple(record(item) for item in sequence(value))
