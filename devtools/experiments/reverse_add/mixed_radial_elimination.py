"""Exact mixed-radial elimination, without sign or temporal closure claims.

The objects here are polynomial-weighted shifted binomial packets

``P(k) * choose(r, k - s)``.

One first-order operator deletes a selected pivot and rewrites every surviving
packet without expanding its binomial row.  This is research arithmetic only:
it neither isolates coefficient signs nor binds a packet to a source cylinder.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb

Polynomial = tuple[Fraction, ...]


@dataclass(frozen=True, slots=True)
class EliminationLimits:
    max_terms: int = 128
    max_steps: int = 127
    max_polynomial_degree: int = 256
    max_polynomial_coefficients: int = 100_000
    max_coefficient_bits: int = 65_536
    max_coefficient_work_bits: int = 8_000_000

    def __post_init__(self) -> None:
        for value in (
            self.max_terms,
            self.max_steps,
            self.max_polynomial_degree,
            self.max_polynomial_coefficients,
            self.max_coefficient_bits,
            self.max_coefficient_work_bits,
        ):
            if type(value) is not int or value <= 0:
                raise ValueError("elimination limits must be positive exact integers")


@dataclass(slots=True)
class EliminationWork:
    steps: int = 0
    input_terms: int = 0
    polynomial_operations: int = 0
    polynomial_coefficients: int = 0
    coefficient_work_bits: int = 0
    peak_polynomial_degree: int = 0
    peak_coefficient_bits: int = 0


def _canonical_polynomial(values: tuple[Fraction, ...]) -> Polynomial:
    if type(values) is not tuple:
        raise TypeError("polynomial coefficients must be a tuple")
    if any(type(value) not in (int, Fraction) for value in values):
        raise TypeError("polynomial coefficients must be exact rationals")
    result = [Fraction(value) for value in values]
    while result and not result[-1]:
        result.pop()
    return tuple(result)


@dataclass(frozen=True, slots=True)
class WeightedBinomial:
    polynomial: Polynomial
    growth: int
    shift: int

    def __post_init__(self) -> None:
        if type(self.growth) is not int or type(self.shift) is not int:
            raise TypeError("weighted binomial coordinates must be exact integers")
        if self.growth < 0:
            raise ValueError("binomial growth must be nonnegative")
        polynomial = _canonical_polynomial(self.polynomial)
        if not polynomial:
            raise ValueError("weighted binomial polynomial must be nonzero")
        object.__setattr__(self, "polynomial", polynomial)

    @property
    def degree(self) -> int:
        return len(self.polynomial) - 1

    @property
    def terminal(self) -> int:
        return self.shift + self.growth


class _Budget:
    def __init__(self, work: EliminationWork, limits: EliminationLimits) -> None:
        self.work = work
        self.limits = limits

    def integer(self, value: int) -> None:
        bits = max(1, abs(value).bit_length())
        self.work.coefficient_work_bits += bits
        self.work.peak_coefficient_bits = max(self.work.peak_coefficient_bits, bits)
        if bits > self.limits.max_coefficient_bits:
            raise ValueError("elimination coefficient size budget exhausted")
        if self.work.coefficient_work_bits > self.limits.max_coefficient_work_bits:
            raise ValueError("elimination coefficient work budget exhausted")

    def fraction(self, value: Fraction) -> None:
        self.integer(value.numerator)
        self.integer(value.denominator)

    def polynomial(self, value: Polynomial) -> None:
        if not value:
            return
        degree = len(value) - 1
        self.work.peak_polynomial_degree = max(self.work.peak_polynomial_degree, degree)
        if degree > self.limits.max_polynomial_degree:
            raise ValueError("elimination polynomial degree budget exhausted")
        self.work.polynomial_coefficients += len(value)
        if self.work.polynomial_coefficients > self.limits.max_polynomial_coefficients:
            raise ValueError("elimination polynomial coefficient budget exhausted")
        for coefficient in value:
            self.fraction(coefficient)

    def preflight_operation(
        self, *, size: int, coefficient_bits: int, arithmetic_terms: int
    ) -> None:
        """Reserve a conservative result before any rational arithmetic."""
        if size <= 0:
            return
        degree = size - 1
        coefficient_bits = max(1, coefficient_bits)
        arithmetic_terms = max(1, arithmetic_terms)
        if degree > self.limits.max_polynomial_degree:
            raise ValueError("elimination polynomial degree budget exhausted")
        if (
            self.work.polynomial_coefficients + size
            > self.limits.max_polynomial_coefficients
        ):
            raise ValueError("elimination polynomial coefficient budget exhausted")
        if coefficient_bits > self.limits.max_coefficient_bits:
            raise ValueError("elimination coefficient size budget exhausted")
        charged_bits = 2 * arithmetic_terms * coefficient_bits
        if (
            self.work.coefficient_work_bits + charged_bits
            > self.limits.max_coefficient_work_bits
        ):
            raise ValueError("elimination coefficient work budget exhausted")
        self.work.polynomial_operations += 1
        self.work.polynomial_coefficients += size
        self.work.coefficient_work_bits += charged_bits
        self.work.peak_polynomial_degree = max(self.work.peak_polynomial_degree, degree)
        self.work.peak_coefficient_bits = max(
            self.work.peak_coefficient_bits, coefficient_bits
        )

    def finish_operation(
        self, value: tuple[Fraction, ...], *, size: int, coefficient_bits: int
    ) -> Polynomial:
        """Check that a precharged conservative bound covered the exact result."""
        value = _canonical_polynomial(value)
        if len(value) > size:
            raise ArithmeticError("elimination polynomial allocation bound was unsound")
        for coefficient in value:
            actual = max(
                1,
                abs(coefficient.numerator).bit_length(),
                coefficient.denominator.bit_length(),
            )
            if actual > coefficient_bits:
                raise ArithmeticError("elimination coefficient bound was unsound")
        return value


def _height(value: Polynomial) -> int:
    return max(
        (
            max(
                1,
                abs(coefficient.numerator).bit_length(),
                coefficient.denominator.bit_length(),
            )
            for coefficient in value
        ),
        default=1,
    )


def _add_values(left: Polynomial, right: Polynomial, size: int) -> tuple[Fraction, ...]:
    return tuple(
        (left[index] if index < len(left) else Fraction())
        + (right[index] if index < len(right) else Fraction())
        for index in range(size)
    )


def _convolve(left: Polynomial, right: Polynomial) -> tuple[Fraction, ...]:
    values = [Fraction() for _ in range(len(left) + len(right) - 1)]
    for i, first in enumerate(left):
        for j, second in enumerate(right):
            values[i + j] += first * second
    return tuple(values)


def _shift_values(value: Polynomial) -> tuple[Fraction, ...]:
    result = [Fraction() for _ in value]
    for degree, coefficient in enumerate(value):
        for power in range(degree + 1):
            result[power] += coefficient * comb(degree, power)
    return tuple(result)


def _scale_values(value: Polynomial, scalar: Fraction) -> tuple[Fraction, ...]:
    return tuple(scalar * coefficient for coefficient in value)


def _add(left: Polynomial, right: Polynomial, budget: _Budget) -> Polynomial:
    size = max(len(left), len(right))
    coefficient_bits = _height(left) + _height(right) + 1
    budget.preflight_operation(
        size=size, coefficient_bits=coefficient_bits, arithmetic_terms=size
    )
    values = _add_values(left, right, size)
    return budget.finish_operation(values, size=size, coefficient_bits=coefficient_bits)


def _subtract(left: Polynomial, right: Polynomial, budget: _Budget) -> Polynomial:
    size = max(len(left), len(right))
    coefficient_bits = _height(left) + _height(right) + 1
    budget.preflight_operation(
        size=size, coefficient_bits=coefficient_bits, arithmetic_terms=size
    )
    values = _add_values(left, tuple(-value for value in right), size)
    return budget.finish_operation(values, size=size, coefficient_bits=coefficient_bits)


def _multiply(left: Polynomial, right: Polynomial, budget: _Budget) -> Polynomial:
    if not left or not right:
        return ()
    size = len(left) + len(right) - 1
    products_per_coefficient = min(len(left), len(right))
    coefficient_bits = (
        products_per_coefficient * (_height(left) + _height(right) + 1)
        + products_per_coefficient.bit_length()
    )
    arithmetic_terms = len(left) * len(right)
    budget.preflight_operation(
        size=size,
        coefficient_bits=coefficient_bits,
        arithmetic_terms=arithmetic_terms,
    )
    values = _convolve(left, right)
    return budget.finish_operation(values, size=size, coefficient_bits=coefficient_bits)


def _shift_one(value: Polynomial, budget: _Budget) -> Polynomial:
    """Return P(k+1) for ascending coefficients of P(k)."""
    if not value:
        return ()
    size = len(value)
    coefficient_bits = size * (_height(value) + size) + size.bit_length()
    arithmetic_terms = size * (size + 1) // 2
    budget.preflight_operation(
        size=size,
        coefficient_bits=coefficient_bits,
        arithmetic_terms=arithmetic_terms,
    )
    result = _shift_values(value)
    return budget.finish_operation(result, size=size, coefficient_bits=coefficient_bits)


def _linear(constant: int, slope: int, budget: _Budget) -> Polynomial:
    coefficient_bits = max(1, abs(constant).bit_length(), abs(slope).bit_length())
    budget.preflight_operation(
        size=2, coefficient_bits=coefficient_bits, arithmetic_terms=2
    )
    values = (Fraction(constant), Fraction(slope))
    return budget.finish_operation(values, size=2, coefficient_bits=coefficient_bits)


def _scale(value: Polynomial, scalar: Fraction, budget: _Budget) -> Polynomial:
    scalar_bits = max(
        1, abs(scalar.numerator).bit_length(), scalar.denominator.bit_length()
    )
    coefficient_bits = _height(value) + scalar_bits
    budget.preflight_operation(
        size=len(value),
        coefficient_bits=coefficient_bits,
        arithmetic_terms=len(value),
    )
    result = _scale_values(value, scalar)
    return budget.finish_operation(
        result, size=len(value), coefficient_bits=coefficient_bits
    )


def _canonical_terms(
    terms: tuple[WeightedBinomial, ...], budget: _Budget
) -> tuple[WeightedBinomial, ...]:
    if type(terms) is not tuple or len(terms) > budget.limits.max_terms:
        raise ValueError("mixed elimination term budget exhausted")
    combined: dict[tuple[int, int], Polynomial] = {}
    for term in terms:
        if type(term) is not WeightedBinomial:
            raise TypeError("mixed elimination requires typed weighted packets")
        term.__post_init__()
        budget.work.input_terms += 1
        budget.integer(term.growth)
        budget.integer(term.shift)
        budget.polynomial(term.polynomial)
        key = term.growth, term.shift
        if key in combined:
            combined[key] = _add(combined[key], term.polynomial, budget)
        else:
            combined[key] = term.polynomial
    return tuple(
        WeightedBinomial(polynomial, growth, shift)
        for (growth, shift), polynomial in combined.items()
        if polynomial
    )


def eliminate_pivot(
    pivot: WeightedBinomial,
    terms: tuple[WeightedBinomial, ...],
    *,
    work: EliminationWork,
    limits: EliminationLimits | None = None,
) -> tuple[WeightedBinomial, ...]:
    """Apply the pivot's first-order operator to supplied weighted packets.

    For ``Pp(k) h_(rp,sp)`` and ``Pi(k) h_(ri,si)``, the survivor is

    ``N_i(k)/(ri+1) * h_(ri+1,si-1)``

    with ``N_i`` exactly as stated in the module's research derivation.  A
    term equal to the pivot cancels.  The returned expression is the operated
    expression, not a sign partition or a source-authorized successor.
    """
    if type(pivot) is not WeightedBinomial or type(terms) is not tuple:
        raise TypeError("mixed elimination requires typed weighted packets")
    pivot.__post_init__()
    budget = _Budget(work, limits or EliminationLimits())
    if len(terms) + 1 > budget.limits.max_terms:
        raise ValueError("mixed elimination term budget exhausted")
    budget.work.input_terms += 1
    budget.integer(pivot.growth)
    budget.integer(pivot.shift)
    budget.polynomial(pivot.polynomial)
    pivot_next = _shift_one(pivot.polynomial, budget)
    pivot_birth = _linear(1 - pivot.shift, 1, budget)  # k + 1 - sp
    pivot_death = _linear(pivot.terminal, -1, budget)  # tp - k
    survivors: list[WeightedBinomial] = []
    for term in terms:
        if type(term) is not WeightedBinomial:
            raise TypeError("mixed elimination requires typed weighted packets")
        term.__post_init__()
        budget.work.input_terms += 1
        budget.integer(term.growth)
        budget.integer(term.shift)
        budget.polynomial(term.polynomial)
        term_next = _shift_one(term.polynomial, budget)
        term_death = _linear(term.terminal, -1, budget)
        term_birth = _linear(1 - term.shift, 1, budget)
        left = _multiply(
            _multiply(pivot.polynomial, pivot_birth, budget),
            _multiply(term_next, term_death, budget),
            budget,
        )
        right = _multiply(
            _multiply(pivot_next, pivot_death, budget),
            _multiply(term.polynomial, term_birth, budget),
            budget,
        )
        numerator = _subtract(left, right, budget)
        if not numerator:
            continue
        expected_degree = pivot.degree + term.degree + 1
        if len(numerator) - 1 > expected_degree:
            raise ArithmeticError("mixed elimination leading terms did not cancel")
        polynomial = _scale(numerator, Fraction(1, term.growth + 1), budget)
        survivors.append(WeightedBinomial(polynomial, term.growth + 1, term.shift - 1))
    if len(survivors) > budget.limits.max_terms:
        raise ValueError("mixed elimination term budget exhausted")
    return tuple(survivors)


def eliminate_chain(
    terms: tuple[WeightedBinomial, ...],
    *,
    work: EliminationWork,
    limits: EliminationLimits | None = None,
) -> tuple[WeightedBinomial, ...]:
    """Iteratively eliminate the first packet until at most one remains."""
    chosen = limits or EliminationLimits()
    budget = _Budget(work, chosen)
    current = _canonical_terms(terms, budget)
    while len(current) > 1:
        if work.steps >= chosen.max_steps:
            raise ValueError("mixed elimination step budget exhausted")
        pivot, rest = current[0], current[1:]
        work.steps += 1
        current = eliminate_pivot(pivot, rest, work=work, limits=chosen)
        current = _canonical_terms(current, budget)
    return current


def evaluate_polynomial(polynomial: Polynomial, k: int) -> Fraction:
    """Evaluate a small retained weight; intended for bounded differential tests."""
    if type(k) is not int:
        raise TypeError("polynomial coordinate must be an exact integer")
    result = Fraction()
    for coefficient in reversed(_canonical_polynomial(polynomial)):
        result = result * k + coefficient
    return result


def evaluate_weighted_binomial(term: WeightedBinomial, k: int) -> Fraction:
    """Evaluate one bounded test point, returning zero outside packet support."""
    if type(term) is not WeightedBinomial or type(k) is not int:
        raise TypeError("weighted packet evaluation requires exact typed input")
    offset = k - term.shift
    if not 0 <= offset <= term.growth:
        return Fraction()
    return evaluate_polynomial(term.polynomial, k) * comb(term.growth, offset)


__all__ = [
    "EliminationLimits",
    "EliminationWork",
    "Polynomial",
    "WeightedBinomial",
    "eliminate_chain",
    "eliminate_pivot",
    "evaluate_polynomial",
    "evaluate_weighted_binomial",
]
