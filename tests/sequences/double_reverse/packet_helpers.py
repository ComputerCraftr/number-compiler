"""Typed boundary readers for independent JSON packet regressions."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.api.json_output import (
    is_object_sequence,
    is_string_object_mapping,
)


def object_mapping(value: object) -> Mapping[str, object]:
    if not is_string_object_mapping(value):
        raise AssertionError("expected a string-keyed JSON object")
    return value


def object_list(value: object) -> list[object]:
    if not is_object_sequence(value) or not isinstance(value, list):
        raise AssertionError("expected a JSON list")
    return value


def integer_field(mapping: Mapping[str, object], key: str) -> int:
    value = mapping.get(key)
    if type(value) is not int:
        raise AssertionError(f"expected integer field {key!r}")
    return value


def string_field(mapping: Mapping[str, object], key: str) -> str:
    value = mapping.get(key)
    if type(value) is not str:
        raise AssertionError(f"expected string field {key!r}")
    return value
