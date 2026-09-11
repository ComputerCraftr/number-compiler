"""Exact source-independent spatial transport over F2.

The homogeneous operator is ``(2*I)**q * (I + S)**r``.  Every positive
``q`` annihilates the F2 source.  Otherwise characteristic-two Frobenius
factors the operator by the set bits of ``r``:

    (I + S)**r = product((I + S**(2**j)) for set bit j of r).

Carry/domain forcing is supplied explicitly by the caller.  Spatial alignment
and growth padding are caller-owned, and affine composition does not infer or
skip the nonlinear domain/parity gates that produce future forcing.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.affine_transport import (
    apply_output_forcing,
    compose_output_forcing,
)

T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class F2SpatialTransport:
    """Canonical compact descriptor for ``(2*I)**q * (I + S)**r`` over F2."""

    no_growths: int = 0
    growths: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.no_growths) is not int
            or type(self.growths) is not int
            or self.no_growths < 0
            or self.growths < 0
        ):
            raise ValueError("F2 transport requires nonnegative exact counts")
        if self.no_growths:
            object.__setattr__(self, "no_growths", 1)
            object.__setattr__(self, "growths", 0)

    @property
    def annihilated(self) -> bool:
        return bool(self.no_growths)

    def then(self, after: F2SpatialTransport) -> F2SpatialTransport:
        """Compose commuting homogeneous transports, applying ``after`` last."""
        if type(after) is not F2SpatialTransport:
            raise TypeError("F2 spatial composition requires the same field")
        return F2SpatialTransport(
            self.no_growths + after.no_growths,
            self.growths + after.growths,
        )

    def coefficient(self, shift: int) -> int:
        """Return the coefficient of ``S**shift`` without expanding the power."""
        if type(shift) is not int:
            raise TypeError("F2 spatial shifts require exact integers")
        if self.annihilated or shift < 0 or shift > self.growths:
            return 0
        return int(shift & ~self.growths == 0)

    def frobenius_factors(self) -> tuple[tuple[int, int], ...]:
        """Return one ``(2**j, 1)`` factor for every set bit of the exponent."""
        if self.annihilated:
            return ()
        remaining = self.growths
        stride = 1
        factors: list[tuple[int, int]] = []
        while remaining:
            if remaining & 1:
                factors.append((stride, 1))
            remaining >>= 1
            stride <<= 1
        return tuple(factors)

    def shifts(self, *, max_terms: int = 4096) -> tuple[tuple[int, int], ...]:
        """Expand a bounded nonzero coefficient support as ``(shift, 1)``."""
        if type(max_terms) is not int or max_terms < 1:
            raise ValueError("F2 expansion requires a positive term budget")
        if self.annihilated:
            return ()
        factors = self.frobenius_factors()
        if 1 << len(factors) > max_terms:
            raise BlockContextBudgetExceeded("F2 transport term budget exceeded")
        offsets = [0]
        for stride, _multiplicity in factors:
            offsets += [offset + stride for offset in offsets]
        return tuple((offset, 1) for offset in offsets)

    def apply(
        self,
        source: T,
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
    ) -> T:
        """Apply through exact F2 callbacks without expanding coefficients."""
        if self.annihilated:
            return add(source, source)
        result = source
        for stride, _multiplicity in self.frobenius_factors():
            result = add(result, shift(result, stride))
        return result

    def apply_with_output_forcing(
        self,
        source: T,
        forcing: T,
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
    ) -> T:
        """Apply the homogeneous operator, then add output-aligned forcing."""
        return add(self.apply(source, shift=shift, add=add), forcing)


@dataclass(frozen=True, slots=True)
class F2AffineTransport(Generic[T]):
    """One homogeneous F2 transport plus output-aligned additive forcing.

    All values passed to callbacks must already inhabit the same spatial
    interval.  In particular, callers must right-pad earlier forcing before
    composing across growth.  Future nonlinear forcing remains caller-owned.
    """

    linear: F2SpatialTransport
    forcing: T

    def __post_init__(self) -> None:
        if type(self.linear) is not F2SpatialTransport:
            raise TypeError("F2 affine transport requires an F2 spatial operator")

    def apply(
        self,
        source: T,
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
    ) -> T:
        return apply_output_forcing(
            source,
            self.forcing,
            apply_linear=lambda value: self.linear.apply(value, shift=shift, add=add),
            add=add,
        )

    def then(
        self,
        after: F2AffineTransport[T],
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
    ) -> F2AffineTransport[T]:
        """Compose exact affine maps using ``A2*f1 + f2`` for the forcing."""
        if type(after) is not F2AffineTransport:
            raise TypeError("F2 affine composition requires the same field")
        forcing = compose_output_forcing(
            self.forcing,
            after.forcing,
            apply_later_linear=lambda value: after.linear.apply(
                value, shift=shift, add=add
            ),
            add=add,
        )
        return F2AffineTransport(self.linear.then(after.linear), forcing)


__all__ = ["F2AffineTransport", "F2SpatialTransport"]
