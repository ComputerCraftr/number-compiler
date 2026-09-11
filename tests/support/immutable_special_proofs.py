"""Reuse immutable special-number proof records within one test process.

The complete aggregate remains a cold subprocess audit.  Once that audit has
returned its frozen dataclass records, later tests in the same module inspect
those records instead of executing the identical proof factories again.  A
focused test which has not run the aggregate still calls its own factory, so
development selection does not acquire the cost of every special audit.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TypeVar, cast

from devtools.experiments.power_numbers.special_successor_generators import (
    special_successor_generator_metrics,
)
from devtools.experiments.power_numbers.special_successor_models import (
    SpecialSuccessorGeneratorMetrics,
)

T = TypeVar("T")
_complete: SpecialSuccessorGeneratorMetrics | None = None


def complete_special_successor_metrics() -> SpecialSuccessorGeneratorMetrics:
    global _complete
    if _complete is None:
        _complete = special_successor_generator_metrics()
    return _complete


def immutable_proof_rows(
    attribute: str,
    factory: Callable[[], tuple[T, ...]],
) -> tuple[T, ...]:
    """Return aggregate records when available, otherwise run one focused oracle."""
    if _complete is None:
        return factory()
    value = getattr(_complete, attribute)
    if type(value) is not tuple:
        raise TypeError(f"aggregate proof field {attribute!r} is not a row tuple")
    return cast("tuple[T, ...]", value)


def immutable_proof_record(attribute: str, factory: Callable[[], T]) -> T:
    """Return one aggregate record without forcing the aggregate in isolation."""
    if _complete is None:
        return factory()
    return cast("T", getattr(_complete, attribute))


__all__ = [
    "complete_special_successor_metrics",
    "immutable_proof_record",
    "immutable_proof_rows",
]
