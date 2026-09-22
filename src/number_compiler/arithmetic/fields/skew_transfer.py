"""Upper triangular transfers; chronological composition over a commutative ring."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from number_compiler.arithmetic.fields.morphism_core import AffineCocycle

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


def integer_dyadic_fiber_action(
    transfer: SkewTransfer[int], origin: int, precision: int
) -> AffineCocycle[int]:
    """Rechart an integral skew on ``origin + 2**precision * Y``.

    Return ``target_origin + gain * Y`` without a parity/valuation itinerary.
    This is arithmetic, not source admission: production callers must obtain
    the transfer and origin from their authenticated source image. In particular
    an odd target and an integral affine equation cannot certify a Collatz branch.
    The zero-gain singleton shortcut needs no enormous source-stride allocation.
    """
    if type(transfer) is not SkewTransfer or any(
        type(v) is not int
        for v in (transfer.upper, transfer.offset, transfer.lower, origin, precision)
    ):
        raise TypeError("integer cylinder rechart requires exact integer fields")
    if precision < 0 or origin < 0 or origin.bit_length() > precision:
        raise ValueError("cylinder origin is outside its canonical dyadic interval")
    lower = transfer.lower
    if lower <= 0 or lower & (lower - 1):
        raise ValueError("cylinder rechart requires a positive dyadic denominator")
    target, remainder = divmod(transfer.upper * origin + transfer.offset, lower)
    if remainder:
        raise ValueError("cylinder origin has a nonintegral image")
    divisions = lower.bit_length() - 1
    if precision >= divisions:
        gain = transfer.upper << (precision - divisions)
    else:
        gain, remainder = divmod(transfer.upper, 1 << (divisions - precision))
        if remainder:
            raise ValueError("cylinder stride has a nonintegral image")
    return AffineCocycle(gain, target)
