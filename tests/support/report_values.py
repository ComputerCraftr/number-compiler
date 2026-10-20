"""Shape assertions for heterogeneous diagnostic reports used in regressions."""

from collections.abc import Mapping, Sequence
from typing import cast


def object_record(value: object) -> dict[str, object]:
    assert isinstance(value, Mapping), "expected a diagnostic record"
    result: dict[str, object] = {}
    for raw_key, raw_item in cast(Mapping[object, object], value).items():
        key: object = raw_key
        item: object = raw_item
        assert isinstance(key, str), "diagnostic record keys must be strings"
        result[key] = item
    return result


def text_values(value: object) -> tuple[str, ...]:
    assert isinstance(value, (list, tuple)), "expected diagnostic labels"
    result: list[str] = []
    for raw_item in cast(Sequence[object], value):
        item: object = raw_item
        assert isinstance(item, str), "diagnostic label must be text"
        result.append(item)
    return tuple(result)
