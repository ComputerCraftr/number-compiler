"""Type-preserving immutable metric record updates."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields, replace
from typing import TypeVar, cast

from number_compiler.resources.metric_records import LedgerMetrics

_MetricT = TypeVar("_MetricT", bound=LedgerMetrics)


def replace_metric(record: _MetricT, values: dict[str, object]) -> _MetricT:
    if not values.keys() <= {item.name for item in fields(record)}:
        raise ValueError("unknown public metric field")
    dynamic_replace = cast(Callable[..., _MetricT], replace)
    return dynamic_replace(record, **values)


__all__ = ["replace_metric"]
