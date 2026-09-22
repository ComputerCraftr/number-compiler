"""Centered homogeneous reverse/add transport over F5.

This is an operator on coordinate functions, not a state or carry quotient.
The caller supplies the observed growth count; no branch itinerary is inferred.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.affine_transport import (
    radix_exponent_factors,
)


@dataclass(frozen=True, slots=True)
class CenteredF5Transport:
    """Canonical ``2**q (U**-1 + U)**r``; U f(x) = f(x+1).

    F5 makes the no-growth count periodic modulo four. Growth degree stays
    exact: this Laurent operator does not claim sector annihilation.
    """

    no_growths: int = 0
    growths: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.no_growths) is not int
            or type(self.growths) is not int
            or self.no_growths < 0
            or self.growths < 0
        ):
            raise ValueError("centered transport requires nonnegative exact counts")
        object.__setattr__(self, "no_growths", self.no_growths % 4)

    def then(self, after: CenteredF5Transport) -> CenteredF5Transport:
        if type(after) is not CenteredF5Transport:
            raise TypeError("centered transport composition requires the same field")
        return CenteredF5Transport(
            self.no_growths + after.no_growths, self.growths + after.growths
        )

    def coefficient(self, offset: int) -> int:
        """One Laurent coefficient in O(log(r)) via base-five digits."""
        if type(offset) is not int:
            raise TypeError("centered offsets require exact integers")
        doubled = offset + self.growths
        if doubled < 0 or doubled > 2 * self.growths or doubled % 2:
            return 0
        r, k = self.growths, doubled // 2
        value = pow(2, self.no_growths, 5)
        while r or k:
            r, digit = divmod(r, 5)
            k, choice = divmod(k, 5)
            if choice > digit:
                return 0
            value = value * comb(digit, choice) % 5
        return value

    def frobenius_factors(self) -> tuple[tuple[int, int], ...]:
        """Return the nonidentity factors encoded by the base-five exponent.

        A pair ``(stride, multiplicity)`` denotes
        ``(U**-stride + U**stride)**multiplicity``.  In characteristic five,
        Frobenius makes the stride at base-five position ``j`` exactly
        ``5**j``.  Multiplicities are therefore in ``1..4`` and the descriptor
        has logarithmic size even when the expanded operator is enormous.
        """
        return radix_exponent_factors(self.growths, 5)

    def shifts(self, *, max_terms: int = 4096) -> tuple[tuple[int, int], ...]:
        """Expand nonzero Frobenius factors only, with a preallocation bound.

        ``r=5**j`` has two terms however large j is. Dense base-five exponents
        can still require r+1 terms and must fail rather than silently expand.
        """
        if type(max_terms) is not int or max_terms < 1:
            raise ValueError("Frobenius expansion requires a positive term budget")
        factors = self.frobenius_factors()
        count = 1
        for _stride, digit in factors:
            count *= digit + 1
            if count > max_terms:
                raise BlockContextBudgetExceeded("centered F5 term budget exceeded")
        terms = [(0, pow(2, self.no_growths, 5))]
        for stride, digit in factors:
            terms = [
                (offset + 2 * stride * choice, coefficient * comb(digit, choice) % 5)
                for choice in range(digit + 1)
                for offset, coefficient in terms
            ]
        return tuple(
            (offset - self.growths, coefficient) for offset, coefficient in terms
        )
