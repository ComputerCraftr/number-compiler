"""Exact source-independent spatial transport over F5.

The homogeneous operator is ``2**q * (I + S)**r``.  It is stored by the two
event counts and applied through characteristic-five Frobenius factors, so a
power such as ``(I + S)**(5**k)`` remains one shift and one addition.

Carry/domain forcing is deliberately supplied by the caller.  In particular,
``then`` composes homogeneous operators only.  For affine steps
``x -> A1*x + f1`` then ``x -> A2*x + f2``, the caller must transport the first
forcing and form ``A2*f1 + f2``.  This module does not infer a carry itinerary
or claim that dynamic forcing disappears under temporal composition.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from number_compiler.arithmetic.polynomials.affine_transport import (
    apply_output_forcing,
    compose_output_forcing,
)
from number_compiler.arithmetic.polynomials.centered_f5 import CenteredF5Transport

T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class F5SpatialTransport:
    """Canonical compact descriptor for ``2**q * (I + S)**r`` over F5."""

    no_growths: int = 0
    growths: int = 0

    def __post_init__(self) -> None:
        centered = CenteredF5Transport(self.no_growths, self.growths)
        object.__setattr__(self, "no_growths", centered.no_growths)
        object.__setattr__(self, "growths", centered.growths)

    def _centered(self) -> CenteredF5Transport:
        return CenteredF5Transport(self.no_growths, self.growths)

    def then(self, after: F5SpatialTransport) -> F5SpatialTransport:
        """Compose commuting homogeneous transports, applying ``after`` last."""
        if type(after) is not F5SpatialTransport:
            raise TypeError("F5 spatial composition requires the same field")
        combined = self._centered().then(after._centered())
        return F5SpatialTransport(combined.no_growths, combined.growths)

    def coefficient(self, shift: int) -> int:
        """Return the coefficient of ``S**shift`` without expanding the power."""
        if type(shift) is not int:
            raise TypeError("F5 spatial shifts require exact integers")
        return self._centered().coefficient(2 * shift - self.growths)

    def frobenius_factors(self) -> tuple[tuple[int, int], ...]:
        """Return ``(stride, multiplicity)`` for nonidentity Frobenius factors."""
        return self._centered().frobenius_factors()

    def shifts(self, *, max_terms: int = 4096) -> tuple[tuple[int, int], ...]:
        """Expand bounded nonzero coefficients as ``(nonnegative shift, value)``."""
        return tuple(
            ((offset + self.growths) // 2, coefficient)
            for offset, coefficient in self._centered().shifts(max_terms=max_terms)
        )

    def apply(
        self,
        source: T,
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
        scale: Callable[[T, int], T],
    ) -> T:
        """Apply through canonical callbacks without expanding polynomial terms.

        ``shift(value, distance)`` must implement zero-padded ``S**distance``
        on the caller's aligned spatial field.  ``add`` and ``scale`` must be
        exact F5 operations and should canonicalize their outputs if the value
        representation is a DAG.
        """
        result = source
        for stride, multiplicity in self.frobenius_factors():
            for _ in range(multiplicity):
                result = add(result, shift(result, stride))
        return scale(result, pow(2, self.no_growths, 5))

    def apply_with_output_forcing(
        self,
        source: T,
        forcing: T,
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
        scale: Callable[[T, int], T],
    ) -> T:
        """Apply the homogeneous operator, then add output-aligned forcing."""
        return add(
            self.apply(source, shift=shift, add=add, scale=scale),
            forcing,
        )


@dataclass(frozen=True, slots=True)
class F5AffineTransport(Generic[T]):
    """One homogeneous F5 transport plus output-aligned additive forcing.

    The source, forcing, and callback results must inhabit the same caller-owned
    spatial interval. A caller composing across a growth boundary must pad and
    align the earlier forcing first. This descriptor does not derive carries,
    domain transitions, Boolean threshold gates, or their future forcing.
    """

    linear: F5SpatialTransport
    forcing: T

    def __post_init__(self) -> None:
        if type(self.linear) is not F5SpatialTransport:
            raise TypeError("F5 affine transport requires an F5 spatial operator")

    def apply(
        self,
        source: T,
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
        scale: Callable[[T, int], T],
    ) -> T:
        """Return ``linear(source) + forcing`` in the caller's aligned space."""
        return apply_output_forcing(
            source,
            self.forcing,
            apply_linear=lambda value: self.linear.apply(
                value, shift=shift, add=add, scale=scale
            ),
            add=add,
        )

    def then(
        self,
        after: F5AffineTransport[T],
        *,
        shift: Callable[[T, int], T],
        add: Callable[[T, T], T],
        scale: Callable[[T, int], T],
    ) -> F5AffineTransport[T]:
        """Compose exact affine maps using ``A2*f1 + f2`` for the forcing."""
        if type(after) is not F5AffineTransport:
            raise TypeError("F5 affine composition requires the same field")
        forcing = compose_output_forcing(
            self.forcing,
            after.forcing,
            apply_later_linear=lambda value: after.linear.apply(
                value, shift=shift, add=add, scale=scale
            ),
            add=add,
        )
        return F5AffineTransport(self.linear.then(after.linear), forcing)


__all__ = ["F5AffineTransport", "F5SpatialTransport"]
