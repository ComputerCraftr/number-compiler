"""Bounded Frobenius/Cartier rewrite for one formal radial factor.

This module describes an identity in formal Cartier sections of an otherwise
unspecified Laurent polynomial. It accepts no source or section evaluator.
It does not bind a source,
construct those child sections, inspect coefficients, discover carries, or
authorize a temporal cylinder clause.

For ``H = 1 + z`` and ``Lambda_e(f) = sum_i f[2*i+e] z**i``, each returned
contribution denotes

``coefficient * 2**no_growth * z**shift * H**growth * Lambda_child_lane(f)``

in ``(Z / 2**bits Z)[z, z**-1]``.  The contribution count is at most
``2 * bits`` and is independent of the radial exponent.
"""

from __future__ import annotations

from dataclasses import dataclass

MAX_RADIAL_SECTION_BITS = 16


def _exact_integer(value: object, label: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{label} must be an exact integer")
    return value


def _two_valuation(value: int) -> int:
    """Return v2(value) for one positive integer."""
    return (value & -value).bit_length() - 1


def _binomial_valuation(n: int, k: int) -> int:
    """Kummer valuation without constructing the binomial coefficient."""
    if k == 0 or k == n:
        return 0
    return k.bit_count() + (n - k).bit_count() - n.bit_count()


def _odd_binomial_residue(n: int, k: int, precision: int) -> tuple[int, int, int]:
    """Return the odd part of binomial(n,k) modulo 2**precision.

    The final two results count numerator/denominator factors and their bit
    sizes. Each factor performs two modular products and one modular inverse.
    These counters exclude shifts, reduction and inverse costs; they are not
    total arithmetic complexity. No integer of binomial size is constructed.
    """
    if precision < 1:
        raise ValueError("odd binomial residue requires positive precision")
    modulus = 1 << precision
    residue = 1
    bit_work = 0
    for step in range(1, k + 1):
        numerator = n - k + step
        denominator = step
        bit_work += numerator.bit_length() + denominator.bit_length()
        numerator >>= _two_valuation(numerator)
        denominator >>= _two_valuation(denominator)
        residue = residue * (numerator % modulus) % modulus
        residue = residue * pow(denominator, -1, modulus) % modulus
    return residue, k, bit_work


@dataclass(frozen=True, slots=True)
class RadialSectionContribution:
    """One formal summand in a modular Cartier lane rewrite."""

    coefficient: int
    shift: int
    no_growth: int
    growth: int
    child_lane: int

    def validate(self, bits: int) -> None:
        for value, label in (
            (self.coefficient, "section coefficient"),
            (self.shift, "section shift"),
            (self.no_growth, "section no-growth exponent"),
            (self.growth, "section growth exponent"),
            (self.child_lane, "section child lane"),
        ):
            _exact_integer(value, label)
        if self.shift < 0 or self.growth < 0:
            raise ValueError("section shifts and growth exponents must be nonnegative")
        if not 0 <= self.no_growth < bits:
            raise ValueError("section no-growth exponent leaves the modular precision")
        if self.child_lane not in (0, 1):
            raise ValueError("section child lane must be zero or one")
        coefficient_modulus = 1 << (bits - self.no_growth)
        if not 0 < self.coefficient < coefficient_modulus:
            raise ValueError("section coefficient is not a normalized residue")
        if not self.coefficient & 1:
            raise ValueError("powers of two must be absorbed into the radial exponent")


@dataclass(frozen=True, slots=True)
class RadialSectionOperator:
    """A formal modular operator, without source or child-expression authority."""

    bits: int
    q: int
    r: int
    lane: int
    contributions: tuple[RadialSectionContribution, ...]
    term_visits: int
    binomial_factor_steps: int
    inspected_operand_bits: int

    def __post_init__(self) -> None:
        for value, label in (
            (self.bits, "section precision"),
            (self.q, "section power-of-two exponent"),
            (self.r, "section Hasse exponent"),
            (self.lane, "section lane"),
            (self.term_visits, "section term visits"),
            (self.binomial_factor_steps, "section binomial factors"),
            (self.inspected_operand_bits, "section inspected operand widths"),
        ):
            _exact_integer(value, label)
        if not 1 <= self.bits <= MAX_RADIAL_SECTION_BITS:
            raise ValueError("section precision is outside the explicit bound")
        if self.q < 0 or self.r < 0:
            raise ValueError("radial exponents must be nonnegative")
        if self.lane not in (0, 1):
            raise ValueError("section lane must be zero or one")
        if type(self.contributions) is not tuple:
            raise TypeError("section contributions must be an immutable tuple")
        if len(self.contributions) > 2 * self.bits:
            raise ValueError("section rewrite exceeds its bounded term count")
        if not 0 <= self.term_visits <= 2 * self.bits:
            raise ValueError("section term work exceeds its explicit bound")
        if self.binomial_factor_steps < 0 or self.inspected_operand_bits < 0:
            raise ValueError("section work counters must be nonnegative")
        for contribution in self.contributions:
            if type(contribution) is not RadialSectionContribution:
                raise TypeError("section operator contains another contribution sort")
            contribution.validate(self.bits)

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def modular_product_calls(self) -> int:
        return 2 * self.binomial_factor_steps

    @property
    def modular_inverse_calls(self) -> int:
        return self.binomial_factor_steps

    @property
    def is_zero(self) -> bool:
        return not self.contributions

    @property
    def is_source_authority(self) -> bool:
        """Formal rewrites deliberately carry no source admission."""
        return False


def construct_radial_section(
    *, bits: int, q: int, r: int, lane: int
) -> RadialSectionOperator:
    """Construct one lane of ``Lambda(2**q * H**r * f)`` modulo ``2**bits``.

    ``f`` and its two sections are formal variables outside this descriptor.
    Construction visits only the bounded Frobenius terms; it never expands
    ``H**r`` or requests a coefficient of ``f``.
    """
    bits = _exact_integer(bits, "section precision")
    q = _exact_integer(q, "section power-of-two exponent")
    r = _exact_integer(r, "section Hasse exponent")
    lane = _exact_integer(lane, "section lane")
    if not 1 <= bits <= MAX_RADIAL_SECTION_BITS:
        raise ValueError("section precision is outside the explicit bound")
    if q < 0 or r < 0:
        raise ValueError("radial exponents must be nonnegative")
    if lane not in (0, 1):
        raise ValueError("section lane must be zero or one")
    if q >= bits:
        return RadialSectionOperator(bits, q, r, lane, (), 0, 0, 0)

    half, odd = divmod(r, 2)
    stop = min(bits - q, half + 1)
    contributions: list[RadialSectionContribution] = []
    term_visits = 0
    multiply_steps = 0
    bit_work = 0
    for j in range(stop):
        remaining = bits - q - j
        valuation = _binomial_valuation(half, j)
        # Account the bounded valuation operands even if the term vanishes.
        bit_work += half.bit_length() + j.bit_length() + (half - j).bit_length()
        if valuation < remaining:
            coefficient, steps, coefficient_work = _odd_binomial_residue(
                half, j, remaining - valuation
            )
            multiply_steps += steps
            bit_work += coefficient_work
        else:
            coefficient = 0
        for t in range(odd + 1):
            term_visits += 1
            if valuation >= remaining:
                continue
            child_lane = (lane - j - t) & 1
            shift = (j + t + child_lane - lane) // 2
            contributions.append(
                RadialSectionContribution(
                    coefficient,
                    shift,
                    q + j + valuation,
                    half - j,
                    child_lane,
                )
            )
    return RadialSectionOperator(
        bits,
        q,
        r,
        lane,
        tuple(contributions),
        term_visits,
        multiply_steps,
        bit_work,
    )


__all__ = [
    "MAX_RADIAL_SECTION_BITS",
    "RadialSectionContribution",
    "RadialSectionOperator",
    "construct_radial_section",
]
