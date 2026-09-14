"""Power-of-two cyclotomic transport and radial/source-annihilation quotients.

This module owns the reverse-add/Collatz-facing 2-adic transport theorems.  It
uses the same canonical polynomial ring primitives as every other cyclotomic
consumer and the repository-wide binary composition kernel.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.polynomials.cyclotomic import is_power_of_two
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing


@dataclass(frozen=True, slots=True)
class PowerTwoCyclotomicTransport:
    """Closed transport summary in ``Phi_(2m)=z**m+1`` for power-of-two ``m``."""

    classes: int
    no_growth: int
    growth: int
    scalar_v2: int
    remainder_growth: int
    exact_zero: bool = False

    def annihilated(self, bits: int) -> bool:
        bits = int(bits)
        if bits <= 0:
            raise ValueError(bits)
        return self.exact_zero or self.scalar_v2 >= bits


@dataclass(frozen=True, slots=True)
class PowerTwoCyclotomicRadialQuotient:
    """Exact radial/unit split of ``2**q (1+z)**r`` in ``z**m+1``.

    ``m=classes`` is a power of two and the coefficient modulus is ``2**bits``.
    The large predictable scalar mode is represented only by its 2-adic
    valuation.  When that valuation is below the requested precision,
    ``unit_residue`` stores the remaining polynomial after dividing the exact
    multiplier by ``2**scalar_v2``.  Multiplying the two pieces reconstructs
    the original cyclotomic multiplier exactly modulo ``2**bits``.

    This is a *derived theorem coordinate*.  It is useful for proving when old
    source information dies and for exposing the slower cyclotomic phase below
    the exponential radial mode; it is not a second sequence state.
    """

    classes: int
    bits: int
    no_growth: int
    growth: int
    scalar_v2: int
    remainder_growth: int
    unit_residue: tuple[int, ...] | None
    exact_zero: bool = False

    def __post_init__(self) -> None:
        m, bits = int(self.classes), int(self.bits)
        q, r = int(self.no_growth), int(self.growth)
        if not is_power_of_two(m) or bits <= 0 or q < 0 or r < 0:
            raise ValueError(self)
        if self.scalar_v2 < 0 or not 0 <= self.remainder_growth < m:
            raise ValueError(self)
        if self.exact_zero or self.scalar_v2 >= bits:
            if self.unit_residue is not None:
                raise ValueError("annihilated radial quotient has no unit remainder")
        elif self.unit_residue is None or len(self.unit_residue) != m:
            raise ValueError("live radial quotient requires one z**m+1 residue")

    @property
    def steps(self) -> int:
        return self.no_growth + self.growth

    @property
    def radial_exponent(self) -> int:
        """Exponent of the common physical ``z=1`` scale ``2**steps``."""
        return self.steps

    @property
    def annihilated(self) -> bool:
        return self.exact_zero or self.scalar_v2 >= self.bits

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "power-two-cyclotomic-radial",
            self.classes,
            self.bits,
            min(self.bits, self.scalar_v2),
            self.remainder_growth,
            self.unit_residue,
            self.exact_zero,
        )

    def multiplier_residue(self) -> tuple[int, ...]:
        """Reconstruct the exact multiplier modulo ``(z**m+1, 2**bits)``."""
        if self.annihilated:
            return (0,) * self.classes
        if self.unit_residue is None:
            raise AssertionError(self)
        modulus = 1 << self.bits
        scale = 1 << self.scalar_v2
        return tuple((scale * value) % modulus for value in self.unit_residue)


def power_two_cyclotomic_radial_quotient(
    classes: int,
    no_growth: int,
    growth: int,
    *,
    bits: int,
) -> PowerTwoCyclotomicRadialQuotient:
    """Return the exact radial/unit quotient of reverse-add linear transport.

    For ``m>=2`` a power of two,

    ``(1+z)**m = 2 U_m(z)  (mod z**m+1)``

    with ``U_m`` a 2-adic unit.  Writing ``r=a*m+b`` gives

    ``2**q(1+z)**r = 2**(q+a) U_m**a (1+z)**b``.

    Only the valuation ``q+a`` belongs to the exponential radial mode.  The
    remainder is computed by binary powering at the *reduced* precision
    ``bits-(q+a)``.  Hence large temporal exponents do not require expanding a
    binomial polynomial or replaying the growth itinerary.
    """
    m, q, r, bits = map(int, (classes, no_growth, growth, bits))
    if not is_power_of_two(m) or q < 0 or r < 0 or bits <= 0:
        raise ValueError((m, q, r, bits))
    transport = power_two_cyclotomic_transport(m, q, r)
    if transport.exact_zero or transport.scalar_v2 >= bits:
        return PowerTwoCyclotomicRadialQuotient(
            m,
            bits,
            q,
            r,
            transport.scalar_v2,
            transport.remainder_growth,
            None,
            transport.exact_zero,
        )
    live_bits = bits - transport.scalar_v2
    modulus = 1 << live_bits
    if m == 1:
        # The only live m=1 case has r=0, because any growth is exact zero.
        unit: tuple[int, ...] = (1 % modulus,)
    else:
        blocks, rem = divmod(r, m)
        # Endpoints of (1+z)^m cancel under z^m=-1.  Every remaining binomial
        # coefficient is even for power-of-two m, so division by two is exact.
        unit_m = [0] * m
        for index in range(1, m):
            coefficient = comb(m, index)
            if coefficient & 1:
                raise AssertionError((m, index, coefficient))
            unit_m[index] = (coefficient // 2) % modulus
        ring = CyclotomicRing(2 * m, modulus)
        unit = ring.power_residue(unit_m, blocks).value
        if rem:
            one_plus_z = ring.reduce((1, 1))
            unit = ring.multiply(unit, ring.power_residue(one_plus_z, rem).value)
    return PowerTwoCyclotomicRadialQuotient(
        m,
        bits,
        q,
        r,
        transport.scalar_v2,
        transport.remainder_growth,
        tuple(unit),
        False,
    )


def power_two_cyclotomic_transport(
    classes: int, no_growth: int, growth: int
) -> PowerTwoCyclotomicTransport:
    """Summarize ``2**q(1+z)**r`` modulo ``Phi_(2m)(z)``.

    ``classes=m`` must be a power of two.  For ``m=1`` the quotient is
    ``Phi_2=z+1`` and one growth kills old state exactly.  For ``m>=2`` the
    coefficient-content valuation is exactly ``q + floor(r/m)``; the remaining
    factor is nonzero modulo two.
    """
    m, q, r = map(int, (classes, no_growth, growth))
    if not is_power_of_two(m) or q < 0 or r < 0:
        raise ValueError((m, q, r))
    if m == 1 and r:
        return PowerTwoCyclotomicTransport(m, q, r, q, 0, True)
    extra, rem = divmod(r, m)
    return PowerTwoCyclotomicTransport(m, q, r, q + extra, rem, False)


def power_two_cyclotomic_annihilated(
    classes: int, no_growth: int, growth: int, *, bits: int
) -> bool:
    return power_two_cyclotomic_transport(classes, no_growth, growth).annihilated(bits)


def power_two_cyclotomic_modulus(radix: int, classes: int) -> int:
    """Return ``Phi_(2m)(radix)=radix**m+1`` for power-of-two ``m``."""
    radix, classes = int(radix), int(classes)
    if radix < 2 or not is_power_of_two(classes):
        raise ValueError((radix, classes))
    return int(pow(radix, classes)) + 1


__all__ = [
    "PowerTwoCyclotomicRadialQuotient",
    "PowerTwoCyclotomicTransport",
    "power_two_cyclotomic_annihilated",
    "power_two_cyclotomic_modulus",
    "power_two_cyclotomic_radial_quotient",
    "power_two_cyclotomic_transport",
]
