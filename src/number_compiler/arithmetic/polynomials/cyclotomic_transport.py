"""Power-of-two cyclotomic transport and radial/source-annihilation quotients.

This module owns the reverse-add/Collatz-facing 2-adic transport theorems.  It
uses the same canonical polynomial ring primitives as every other cyclotomic
consumer and the repository-wide binary composition kernel.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass, field
from math import comb
from typing import Final

from number_compiler.arithmetic.polynomials.cyclotomic import is_power_of_two
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing

_RADIAL_ISSUER = object()
_MULTIPLIER_KEY_VERSION: Final[str] = "power-two-cyclotomic-multiplier-v2"
_RadialSeal = tuple[int, int, int, int, int, int, tuple[int, ...] | None, bool]


@dataclass(frozen=True, slots=True)
class PowerTwoCyclotomicTransport:
    """Closed transport summary in ``Phi_(2m)=z**m+1`` for power-of-two ``m``."""

    classes: int
    no_growth: int
    growth: int
    scalar_v2: int
    remainder_growth: int
    exact_zero: bool = False

    def __post_init__(self) -> None:
        if (
            any(
                type(value) is not int
                for value in (
                    self.classes,
                    self.no_growth,
                    self.growth,
                    self.scalar_v2,
                    self.remainder_growth,
                )
            )
            or type(self.exact_zero) is not bool
        ):
            raise TypeError("cyclotomic transport requires exact coordinates")
        if not is_power_of_two(self.classes) or self.no_growth < 0 or self.growth < 0:
            raise ValueError("invalid cyclotomic transport source")
        zero = self.classes == 1 and self.growth > 0
        valuation = (
            self.no_growth if zero else self.no_growth + self.growth // self.classes
        )
        remainder = 0 if zero else self.growth % self.classes
        if (self.scalar_v2, self.remainder_growth, self.exact_zero) != (
            valuation,
            remainder,
            zero,
        ):
            raise ValueError("cyclotomic transport differs from its exact exponents")

    def annihilated(self, bits: int) -> bool:
        if type(bits) is not int:
            raise TypeError("cyclotomic precision requires an exact integer")
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
    _checked: InitVar[object] = None
    _verified: _RadialSeal | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def __post_init__(self, _checked: object = None) -> None:
        integer_coordinates = (
            self.classes,
            self.bits,
            self.no_growth,
            self.growth,
            self.scalar_v2,
            self.remainder_growth,
        )
        if any(type(value) is not int for value in integer_coordinates):
            raise TypeError("radial quotient coordinates require exact integers")
        if type(self.exact_zero) is not bool:
            raise TypeError("radial quotient exact_zero must be Boolean")
        if self.unit_residue is not None and (
            type(self.unit_residue) is not tuple
            or any(type(value) is not int for value in self.unit_residue)
        ):
            raise TypeError("radial quotient residue must be an exact integer tuple")

        m, bits = self.classes, self.bits
        q, r = self.no_growth, self.growth
        if not is_power_of_two(m) or bits <= 0 or q < 0 or r < 0:
            raise ValueError(self)
        transport = power_two_cyclotomic_transport(m, q, r)
        if (
            self.exact_zero != transport.exact_zero
            or self.scalar_v2 != transport.scalar_v2
            or self.remainder_growth != transport.remainder_growth
        ):
            raise ValueError(
                "radial quotient derived coordinates disagree with exponents"
            )
        if self.scalar_v2 < 0 or not 0 <= self.remainder_growth < m:
            raise ValueError(self)
        if self.exact_zero or self.scalar_v2 >= bits:
            if self.unit_residue is not None:
                raise ValueError("annihilated radial quotient has no unit remainder")
        elif self.unit_residue is None or len(self.unit_residue) != m:
            raise ValueError("live radial quotient requires one z**m+1 residue")
        else:
            reduced_bits = bits - self.scalar_v2
            if any(
                value < 0 or value.bit_length() > reduced_bits
                for value in self.unit_residue
            ):
                raise ValueError(
                    "radial quotient residue is outside its reduced modulus"
                )
        coordinates = (
            m,
            bits,
            q,
            r,
            self.scalar_v2,
            self.remainder_growth,
            self.unit_residue,
            self.exact_zero,
        )
        if self._verified is not None:
            if coordinates != self._verified:
                raise ValueError("radial quotient changed after validation")
            return
        if not self.annihilated and _checked is not _RADIAL_ISSUER:
            expected = _live_radial_unit(m, r, bits - self.scalar_v2)
            if self.unit_residue != expected:
                raise ValueError(
                    "radial quotient unit differs from its exact multiplier"
                )
        object.__setattr__(self, "_verified", coordinates)

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
    def canonical_key(
        self,
    ) -> tuple[
        str,
        int,
        int,
        int,
        tuple[int, ...] | None,
    ]:
        """Identity of the multiplier at this precision, excluding its derivation.

        Annihilation has one identity in each ring, regardless of which growth
        or scalar factor killed the source. Raw exponents remain occurrence
        provenance; this key alone does not authenticate their source action.
        """
        return (
            _MULTIPLIER_KEY_VERSION,
            self.classes,
            self.bits,
            self.bits if self.annihilated else self.scalar_v2,
            None if self.annihilated else self.unit_residue,
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


def _live_radial_unit(m: int, r: int, live_bits: int) -> tuple[int, ...]:
    """Compute the exact unit once; no source or occurrence cache is involved."""
    modulus = 1 << live_bits
    if m == 1:
        return (1 % modulus,)
    blocks, rem = divmod(r, m)
    if not blocks:
        # No full cyclotomic block is used. In particular, the identity must
        # not construct m binomial coefficients and a ring merely to power 0.
        return tuple(comb(rem, i) % modulus for i in range(rem + 1)) + (0,) * (
            m - rem - 1
        )
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
    return tuple(unit)


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
    if any(type(value) is not int for value in (classes, no_growth, growth, bits)):
        raise TypeError("cyclotomic coordinates require exact integers")
    m, q, r = classes, no_growth, growth
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
    unit = _live_radial_unit(m, r, live_bits)
    return PowerTwoCyclotomicRadialQuotient(
        m,
        bits,
        q,
        r,
        transport.scalar_v2,
        transport.remainder_growth,
        unit,
        False,
        _checked=_RADIAL_ISSUER,
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
    if any(type(value) is not int for value in (classes, no_growth, growth)):
        raise TypeError("cyclotomic coordinates require exact integers")
    m, q, r = classes, no_growth, growth
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
    if type(radix) is not int or type(classes) is not int:
        raise TypeError("cyclotomic coordinates require exact integers")
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
