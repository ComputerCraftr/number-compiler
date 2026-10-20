"""Exact algebra on *projection outputs* rather than source digit states.

A projection field is a finite symbol word produced by a sequence compiler:
prime bits, carry-action symbols, Collatz valuations, modular residue digits,
etc.  This module supplies exact block homomorphisms that can be composed or
powered without expanding long runs:

* binomial moments, whose concatenation is the Vandermonde shift;
* cyclotomic polynomial residues, whose concatenation is polynomial shift;
* the existing ``(z+1)`` primary jet and canonical RLE/SLP word metrics.

These are theorem interfaces, not alternative semantic source states.  A
caller must still prove that the requested projection can be recovered from a
chosen interface; merely changing coordinates does not constitute a quotient.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.automata.program_word import from_runs, word_metrics
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radix import bit_width, symbol_runs
from number_compiler.arithmetic.polynomials.cyclotomic import (
    cyclotomic_coefficients,
    cyclotomic_value,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.polynomial import (
    polynomial_divide_exact,
    polynomial_multiply,
)
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetBlock,
    primary_jet_from_runs,
)


@dataclass(frozen=True, slots=True)
class BinomialMomentBlock:
    """Exact finite binomial moments of a projection word.

    ``moments[r] = sum_i binom(i,r)*a_i (mod modulus)``.  Concatenation is a
    closed triangular action by Vandermonde's identity.
    """

    degree: int
    modulus: int
    length: int
    moments: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        if (
            self.degree <= 0
            or self.modulus <= 1
            or self.length < 0
            or self.compositions < 0
        ):
            raise ValueError(self)
        if len(self.moments) != self.degree:
            raise ValueError((len(self.moments), self.degree))
        object.__setattr__(
            self, "moments", tuple(int(x) % self.modulus for x in self.moments)
        )

    @classmethod
    def identity(cls, degree: int = 4, modulus: int = 32) -> BinomialMomentBlock:
        return cls(int(degree), int(modulus), 0, (0,) * int(degree), 0)

    @classmethod
    def digit(
        cls, value: int, *, degree: int = 4, modulus: int = 32
    ) -> BinomialMomentBlock:
        return cls(
            int(degree),
            int(modulus),
            1,
            (int(value) % int(modulus),) + (0,) * (int(degree) - 1),
            0,
        )

    def then(self, other: BinomialMomentBlock) -> BinomialMomentBlock:
        if (self.degree, self.modulus) != (other.degree, other.modulus):
            raise ValueError((self, other))
        out: list[int] = []
        for r in range(self.degree):
            shifted = sum(
                comb(self.length, r - s) * other.moments[s] for s in range(r + 1)
            )
            out.append((self.moments[r] + shifted) % self.modulus)
        return BinomialMomentBlock(
            self.degree,
            self.modulus,
            self.length + other.length,
            tuple(out),
            self.compositions + other.compositions + 1,
        )

    def power_block(self, exponent: int) -> BinomialMomentBlock:
        powered = binary_power(
            self,
            exponent,
            identity=BinomialMomentBlock.identity(self.degree, self.modulus),
            compose=BinomialMomentBlock.then,
        )
        result = powered.value
        return BinomialMomentBlock(
            result.degree,
            result.modulus,
            result.length,
            result.moments,
            powered.compositions,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "projection-binomial",
            self.degree,
            self.modulus,
            self.length,
            self.moments,
        )

    @property
    def description_bits(self) -> int:
        cb = bit_width(self.modulus - 1)
        return (
            bit_width(self.degree)
            + bit_width(self.modulus)
            + bit_width(self.length)
            + self.degree * cb
        )


@dataclass(frozen=True, slots=True)
class PaddedRadixEvaluation:
    """Exact alternate-radix evaluation of one fixed-width symbol word.

    ``values`` are read in ordinary most-significant-first string order.  The
    integer value alone forgets leading zeros; ``length`` restores them, making
    ``(radix, length, value)`` a lossless coordinate whenever every symbol is a
    canonical radix digit.  This object is a derived theorem/research view, not
    an additional sequence state.
    """

    radix: int
    length: int
    value: int

    def __post_init__(self) -> None:
        if self.radix < 2 or self.length < 0 or self.value < 0:
            raise ValueError(self)
        if self.value >= self.radix**self.length and self.length:
            raise ValueError("value does not fit padded radix width")
        if self.length == 0 and self.value:
            raise ValueError("empty padded word must evaluate to zero")

    @classmethod
    def from_msf_values(
        cls, values: Sequence[int], *, radix: int
    ) -> PaddedRadixEvaluation:
        radix = int(radix)
        digits = tuple(map(int, values))
        if radix < 2 or any(not 0 <= digit < radix for digit in digits):
            raise ValueError((digits, radix))
        value = 0
        for digit in digits:
            value = value * radix + digit
        return cls(radix, len(digits), value)

    def recover_msf_values(self) -> tuple[int, ...]:
        if not self.length:
            return ()
        value = self.value
        out = [0] * self.length
        for index in range(self.length - 1, -1, -1):
            value, out[index] = divmod(value, self.radix)
        if value:
            raise AssertionError((self, value))
        return tuple(out)

    @property
    def leading_zero_padding(self) -> int:
        values = self.recover_msf_values()
        count = 0
        for value in values:
            if value:
                break
            count += 1
        return count

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("padded-radix-evaluation", self.radix, self.length, self.value)

    @property
    def description_bits(self) -> int:
        return bit_width(self.radix) + bit_width(self.length) + bit_width(self.value)


def padded_radix_evaluation(
    values: Sequence[int], *, radix: int
) -> PaddedRadixEvaluation:
    return PaddedRadixEvaluation.from_msf_values(values, radix=radix)


@dataclass(frozen=True, slots=True)
class BoundedCyclotomicFactorization:
    """Lossless factorization of a padded word polynomial through bounded orders.

    The source word is interpreted in most-significant-first order, so its
    associated polynomial is exactly the base-evaluation polynomial

        ``W(z) = d_0*z^(L-1) + ... + d_(L-1)``.

    ``leading_zero_padding`` retains the zeros integer evaluation would lose;
    ``trailing_zero_shift`` stores the monomial ``z**k``.  Every cyclotomic
    factor with order <= ``order_limit`` is divided out exactly and the explicit
    residual keeps the representation lossless even when the factor search is
    deliberately bounded.  Different order limits are research coordinates,
    not interchangeable semantic keys.
    """

    length: int
    order_limit: int
    leading_zero_padding: int
    trailing_zero_shift: int
    factors: tuple[tuple[int, int], ...]
    residual_lsf: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.length < 0 or self.order_limit < 1:
            raise ValueError(self)
        if self.leading_zero_padding < 0 or self.trailing_zero_shift < 0:
            raise ValueError(self)
        if self.leading_zero_padding + self.trailing_zero_shift > self.length:
            raise ValueError(self)
        if not self.residual_lsf:
            raise ValueError("residual polynomial must be explicit")
        previous = 1
        for order, exponent in self.factors:
            if order <= previous or order > self.order_limit or exponent <= 0:
                raise ValueError(self.factors)
            previous = order

    @property
    def zero_word(self) -> bool:
        return self.residual_lsf == (0,)

    @property
    def factor_degree(self) -> int:
        return sum(
            (len(cyclotomic_coefficients(order)) - 1) * exponent
            for order, exponent in self.factors
        )

    @property
    def active_degree(self) -> int:
        if self.zero_word:
            return 0
        return max(
            0, self.length - self.leading_zero_padding - self.trailing_zero_shift - 1
        )

    @property
    def factor_degree_ratio(self) -> float:
        return self.factor_degree / self.active_degree if self.active_degree else 0.0

    @property
    def fully_cyclotomic(self) -> bool:
        return bool(self.factors) and self.residual_lsf in ((1,), (-1,))

    def recover_msf_values(self) -> tuple[int, ...]:
        if self.zero_word:
            return (0,) * self.length
        core = tuple(self.residual_lsf)
        for order, exponent in self.factors:
            factor = cyclotomic_coefficients(order)
            for _ in range(exponent):
                core = polynomial_multiply(core, factor)
        coefficients = (
            (0,) * self.trailing_zero_shift + core + (0,) * self.leading_zero_padding
        )
        if len(coefficients) != self.length:
            raise AssertionError((self, len(coefficients)))
        return tuple(reversed(coefficients))

    def evaluated_cyclotomic_factor(self, radix: int) -> int:
        radix = int(radix)
        if radix < 2:
            raise ValueError(radix)
        out = 1
        for order, exponent in self.factors:
            out *= cyclotomic_value(order, radix) ** exponent
        return out

    @property
    def description_bits(self) -> int:
        bits = (
            bit_width(self.length)
            + bit_width(self.order_limit)
            + bit_width(self.leading_zero_padding)
            + bit_width(self.trailing_zero_shift)
            + bit_width(len(self.factors))
            + bit_width(len(self.residual_lsf))
        )
        for order, exponent in self.factors:
            bits += bit_width(order) + bit_width(exponent)
        for coefficient in self.residual_lsf:
            bits += bit_width(abs(coefficient)) + int(coefficient < 0)
        return bits


def bounded_cyclotomic_factorization(
    values: Sequence[int], *, order_limit: int = 64
) -> BoundedCyclotomicFactorization:
    """Factor one padded MSF word through all exact ``Phi_n``, ``2<=n<=limit``."""
    digits = tuple(map(int, values))
    order_limit = int(order_limit)
    if order_limit < 1:
        raise ValueError(order_limit)
    length = len(digits)
    if not digits or not any(digits):
        return BoundedCyclotomicFactorization(
            length,
            order_limit,
            length,
            0,
            (),
            (0,),
        )

    leading = 0
    while leading < length and digits[leading] == 0:
        leading += 1
    trailing = 0
    while trailing < length - leading and digits[length - 1 - trailing] == 0:
        trailing += 1
    core_msf = digits[leading : length - trailing if trailing else length]
    residual = tuple(reversed(core_msf))
    factors: list[tuple[int, int]] = []
    for order in range(2, order_limit + 1):
        phi = cyclotomic_coefficients(order)
        exponent = 0
        while len(phi) <= len(residual):
            quotient = polynomial_divide_exact(residual, phi)
            if quotient is None:
                break
            residual = quotient
            exponent += 1
        if exponent:
            factors.append((order, exponent))
    result = BoundedCyclotomicFactorization(
        length,
        order_limit,
        leading,
        trailing,
        tuple(factors),
        tuple(residual),
    )
    if result.recover_msf_values() != digits:
        raise AssertionError((digits, result))
    return result


def offset_bit_planes(values: Sequence[int]) -> tuple[int, tuple[tuple[int, ...], ...]]:
    """Return a reversible scalar-offset + binary-plane view of an integer field.

    This is intentionally ephemeral derived instrumentation.  It lets ternary
    Collatz carries and signed/multi-valued convolution carries reuse the same
    0/1 projection algebra without introducing a retained parallel carry state.
    """
    field = tuple(map(int, values))
    if not field:
        raise ValueError("bit-plane field must be nonempty")
    offset = min(field)
    shifted = tuple(value - offset for value in field)
    width = max(shifted).bit_length()
    planes = tuple(
        tuple((value >> bit) & 1 for value in shifted) for bit in range(width)
    )
    return offset, planes


def reconstruct_offset_bit_planes(
    offset: int, length: int, planes: Sequence[Sequence[int]]
) -> tuple[int, ...]:
    offset, length = int(offset), int(length)
    if length <= 0:
        raise ValueError(length)
    ps = tuple(tuple(map(int, plane)) for plane in planes)
    if any(
        len(plane) != length or any(bit not in (0, 1) for bit in plane) for plane in ps
    ):
        raise ValueError((length, ps))
    return tuple(
        offset + sum(plane[index] << bit for bit, plane in enumerate(ps))
        for index in range(length)
    )


@dataclass(frozen=True, slots=True)
class ProjectionFieldSummary:
    length: int
    run_count: int
    word_nodes: int
    word_description_bits: int
    primary_jet: PrimaryJetBlock
    binomial_moments: BinomialMomentBlock
    cyclotomic_projection: tuple[CyclotomicDigitBlock, ...]

    @property
    def theorem_description_bits(self) -> int:
        return (
            self.primary_jet.description_bits
            + self.binomial_moments.description_bits
            + sum(x.description_bits for x in self.cyclotomic_projection)
        )


def binomial_moments_from_runs(
    runs: Iterable[tuple[int, int]], *, degree: int = 4, modulus: int = 32
) -> BinomialMomentBlock:
    out = BinomialMomentBlock.identity(degree, modulus)
    for symbol, count in runs:
        count = int(count)
        if count < 0:
            raise ValueError(count)
        if count:
            out = out.then(
                BinomialMomentBlock.digit(
                    int(symbol), degree=degree, modulus=modulus
                ).power_block(count)
            )
    return out


def binomial_moments_from_values(
    values: Sequence[int], *, degree: int = 4, modulus: int = 32
) -> BinomialMomentBlock:
    return binomial_moments_from_runs(
        symbol_runs(values), degree=degree, modulus=modulus
    )


def cyclotomic_jet_from_runs(
    runs: Iterable[tuple[int, int]],
    *,
    order: int = 2,
    power: int = 1,
    modulus: int = 32,
) -> CyclotomicDigitBlock:
    out = CyclotomicDigitBlock.identity(order, modulus, power=power)
    for symbol, count in runs:
        count = int(count)
        if count < 0:
            raise ValueError(count)
        if count:
            out = out.then(
                CyclotomicDigitBlock.digit(
                    int(symbol),
                    order=order,
                    power=power,
                    modulus=modulus,
                ).power_block(count)
            )
    return out


def cyclotomic_jet_from_values(
    values: Sequence[int], *, order: int = 2, power: int = 1, modulus: int = 32
) -> CyclotomicDigitBlock:
    # The coefficients already are an explicit source sequence. Reduce that
    # polynomial once instead of constructing one digit block per run and
    # repeatedly exponentiating/concatenating them. The run constructor stays
    # available for compressed inputs whose expanded width is intentionally
    # unavailable.
    return CyclotomicDigitBlock.from_coefficients(
        values,
        order=order,
        power=power,
        modulus=modulus,
        length=len(values),
    )


def projection_field_summary_from_runs(
    runs: Iterable[tuple[int, int]],
    *,
    degree: int = 4,
    modulus: int = 32,
    cyclotomic_orders: Sequence[int] = (2, 4, 8),
) -> ProjectionFieldSummary:
    runs = tuple((int(s), int(n)) for s, n in runs if int(n) > 0)
    word = from_runs(runs)
    metrics = word_metrics(word)
    return ProjectionFieldSummary(
        int(metrics["length"]),
        int(metrics["runs"]),
        int(metrics["nodes"]),
        int(metrics["description_bits"]),
        primary_jet_from_runs(runs, degree=degree, modulus=modulus),
        binomial_moments_from_runs(runs, degree=degree, modulus=modulus),
        tuple(
            cyclotomic_jet_from_runs(runs, order=o, power=1, modulus=modulus)
            for o in cyclotomic_orders
        ),
    )


def projection_field_summary_from_values(
    values: Sequence[int],
    *,
    degree: int = 4,
    modulus: int = 32,
    cyclotomic_orders: Sequence[int] = (2, 4, 8),
) -> ProjectionFieldSummary:
    return projection_field_summary_from_runs(
        symbol_runs(values),
        degree=degree,
        modulus=modulus,
        cyclotomic_orders=cyclotomic_orders,
    )


__all__ = [
    "BinomialMomentBlock",
    "BoundedCyclotomicFactorization",
    "PaddedRadixEvaluation",
    "ProjectionFieldSummary",
    "binomial_moments_from_runs",
    "binomial_moments_from_values",
    "bounded_cyclotomic_factorization",
    "cyclotomic_jet_from_runs",
    "cyclotomic_jet_from_values",
    "offset_bit_planes",
    "padded_radix_evaluation",
    "projection_field_summary_from_runs",
    "projection_field_summary_from_values",
    "reconstruct_offset_bit_planes",
]
