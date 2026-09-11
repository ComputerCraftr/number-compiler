"""Compact Hensel-lift markers for cyclotomic digit coordinates."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


def _centered_residue(value: int, modulus: int) -> int:
    """Canonical balanced representative in ``[-q/2, q/2)`` for even ``q``."""
    q = int(modulus)
    value = int(value) % q
    if q <= 1:
        raise ValueError(q)
    return value - q if value >= (q + 1) // 2 else value


def _signed_tuple(values: Sequence[int], modulus: int, sign: int) -> tuple[int, ...]:
    q = int(modulus)
    sign = int(sign)
    if sign not in (-1, 1):
        raise ValueError(sign)
    return tuple(_centered_residue(sign * int(value), q) for value in values)


@dataclass(frozen=True, slots=True)
class CyclotomicLiftMarker:
    """Compact signed marker for one binary Hensel lift of a cyclotomic jet.

    ``lower`` lives modulo ``2**k`` and ``upper`` modulo ``2**(k+1)``.  The
    full next precision layer would contain one extra bit per quotient-ring
    coefficient.  This marker deliberately does *not* retain that layer.  It
    keeps only logarithmic scalar summaries of where the balanced lift first
    changes and which signed/radix direction that missing information takes.

    For unfactored ``Phi_1/Phi_2`` jets the comparison is made in the natural
    local linear coordinate (``z-1`` / ``z+1``).  For other primary factors it
    uses the factor coefficient basis.  ``sign_invariant`` jointly
    canonicalizes ``x`` and ``-x`` before comparison, so a valid Mersenne
    ``x ~ -x`` quotient is never undone merely to recover lift orientation.
    """

    order: int
    power: int
    lower_modulus: int
    degree: int
    first_change: int | None
    last_change: int | None
    change_count: int
    first_orientation: int
    radix_orientation: int
    radix_valuation: int | None
    radix_magnitude_bits: int
    support_moment: int
    signed_moment: int
    sign_invariant: bool = False

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "cyclotomic-lift-marker",
            self.order,
            self.power,
            self.lower_modulus,
            self.degree,
            self.first_change,
            self.last_change,
            self.change_count,
            self.first_orientation,
            self.radix_orientation,
            self.radix_valuation,
            self.radix_magnitude_bits,
            self.support_moment,
            self.signed_moment,
            self.sign_invariant,
        )

    @property
    def description_bits(self) -> int:
        positional = bit_width(self.degree + 1)
        return (
            bit_width(self.order)
            + bit_width(self.power)
            + bit_width(self.lower_modulus)
            + bit_width(self.degree)
            + 2 * positional
            + bit_width(self.change_count)
            + 4
            + bit_width(0 if self.radix_valuation is None else self.radix_valuation + 1)
            + bit_width(self.radix_magnitude_bits)
            + bit_width(abs(self.support_moment))
            + bit_width(abs(self.signed_moment))
        )


def cyclotomic_binary_lift_marker(
    lower: CyclotomicDigitBlock,
    upper: CyclotomicDigitBlock,
    *,
    radix: int = 2,
    sign_invariant: bool = False,
) -> CyclotomicLiftMarker:
    """Return the compact balanced marker for ``2**k -> 2**(k+1)``.

    This is a *projection* of the missing Hensel digit, not another full jet.
    It is exact for the reported marker scalars and intentionally irreversible.
    """
    q = int(lower.modulus)
    Q = int(upper.modulus)
    radix = int(radix)
    if q < 2 or q & (q - 1) or Q != 2 * q or radix <= 1:
        raise ValueError((q, Q, radix))
    if (
        lower.order != upper.order
        or lower.power != upper.power
        or lower.length != upper.length
        or lower.degree != upper.degree
    ):
        raise ValueError((lower.module_key, upper.module_key))
    if (lower.factor is None) != (upper.factor is None):
        raise ValueError("factor/nonfactor lift mismatch")
    if lower.factor is not None:
        if upper.factor is None:
            raise AssertionError("factor lift mismatch")
        if len(lower.factor) != len(upper.factor):
            raise ValueError((lower.factor, upper.factor))
        if tuple(int(v) % q for v in upper.factor) != tuple(
            int(v) % q for v in lower.factor
        ):
            raise ValueError(("factor-does-not-lift", lower.factor, upper.factor))
        lower_values = lower.residue
        upper_values = upper.residue
    elif lower.order in (1, 2):
        lower_values = lower.local_linear_coefficients
        upper_values = upper.local_linear_coefficients
    else:
        lower_values = lower.residue
        upper_values = upper.residue

    signs = (-1, 1) if sign_invariant else (1,)
    candidates: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    for sign in signs:
        lo = _signed_tuple(lower_values, q, sign)
        hi = _signed_tuple(upper_values, Q, sign)
        if all((b - a) % q == 0 for a, b in zip(lo, hi, strict=True)):
            candidates.append((lo, hi))
    if not candidates:
        raise ValueError("upper coordinate does not Hensel-lift lower coordinate")
    # Canonicalize the global +/- orbit jointly; never choose unrelated signs
    # at the two precisions.
    lo, hi = min(candidates, key=lambda pair: (pair[1], pair[0]))
    layer = tuple((b - a) // q for a, b in zip(lo, hi, strict=True))
    support = tuple(index for index, value in enumerate(layer) if value)
    if support:
        first: int | None = support[0]
        last: int | None = support[-1]
        first_orientation = -1 if layer[support[0]] < 0 else 1
    else:
        first = last = None
        first_orientation = 0
    support_moment = sum(support)
    signed_moment = sum((index + 1) * value for index, value in enumerate(layer))
    radix_delta = sum(value * (radix**index) for index, value in enumerate(layer))
    if radix_delta:
        radix_orientation = -1 if radix_delta < 0 else 1
        magnitude = abs(radix_delta)
        radix_valuation = (magnitude & -magnitude).bit_length() - 1
        radix_magnitude_bits = magnitude.bit_length()
    else:
        radix_orientation = 0
        radix_valuation = None
        radix_magnitude_bits = 0
    return CyclotomicLiftMarker(
        lower.order,
        lower.power,
        q,
        lower.degree,
        first,
        last,
        len(support),
        first_orientation,
        radix_orientation,
        radix_valuation,
        radix_magnitude_bits,
        support_moment,
        signed_moment,
        bool(sign_invariant),
    )


__all__ = ["CyclotomicLiftMarker", "cyclotomic_binary_lift_marker"]
