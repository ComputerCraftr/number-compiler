"""Construct dataclass test records from dynamically selected field mutations."""

from collections.abc import Callable, Mapping
from dataclasses import is_dataclass, replace
from typing import TypeVar, cast

RecordT = TypeVar("RecordT")


def replace_record(record: RecordT, changes: Mapping[str, object]) -> RecordT:
    """Keep constructor validation when an adversarial test selects field names."""
    if not is_dataclass(record) or isinstance(record, type):
        raise TypeError("a dataclass instance is required")
    constructor = cast(Callable[..., RecordT], replace)
    return constructor(record, **changes)
