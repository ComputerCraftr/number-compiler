"""Upper triangular transfers; chronological composition over a commutative ring."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class SkewTransfer(Generic[T]):
    upper: T
    offset: T
    lower: T

    def then(
        self,
        after: SkewTransfer[T],
        *,
        multiply: Callable[[T, T], T],
        add: Callable[[T, T], T],
    ) -> SkewTransfer[T]:
        """Matrix(after) * Matrix(self); neither projection becomes an ActionID."""
        return SkewTransfer(
            multiply(after.upper, self.upper),
            add(multiply(after.upper, self.offset), multiply(self.lower, after.offset)),
            multiply(after.lower, self.lower),
        )
