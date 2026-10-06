"""Cyclotomic digit-field quotients shared by reverse-add and special-number probes.

The reverse-add pair polynomial uses the spatial shift variable ``z``.  Growth
multiplies old state by ``1+z`` while no-growth multiplies it by ``2``.  The
negacyclic quotients ``z**m+1`` used by the earlier release become especially
structured when ``m`` is a power of two::

    z**m + 1 = Phi_(2m)(z).

For ``m >= 2`` a power of two,

    (1+z)**m = 2 * U_m(z)      mod Phi_(2m)(z),

and ``U_m`` is a 2-adic unit.  Consequently the exact coefficient-content
valuation of ``2**q (1+z)**r`` in this cyclotomic channel is
``q + floor(r/m)``.  This turns a kernel-expansion test into a constant-size
valuation theorem.

The same polynomials evaluated at arbitrary radices provide the exact bridge
used by padded projection-word reinterpretation: if ``Phi_n(z)`` divides a
projection polynomial ``P(z)``, then ``Phi_n(b)`` divides ``P(b)`` for every
integer radix ``b``.  Width/padding is a separate coordinate because integer
evaluation alone discards leading zero digits.
"""

from __future__ import annotations

from functools import cache

from number_compiler.arithmetic.number_theory import smallest_factor
from number_compiler.arithmetic.polynomials.polynomial import (
    evaluate_polynomial,
    polynomial_divide_exact,
    polynomial_power,
)


def is_power_of_two(value: int) -> bool:
    value = int(value)
    return value > 0 and value & (value - 1) == 0


def _prime_power_base(value: int) -> int | None:
    """Return ``p`` when ``value`` is a positive power of one prime ``p``."""
    value = int(value)
    if value <= 1:
        return None
    p = smallest_factor(value)
    if p is None:
        return value
    n = value
    while n % p == 0:
        n //= p
    return p if n == 1 else None


@cache
def cyclotomic_coefficients(order: int) -> tuple[int, ...]:
    """Return LSF integer coefficients of the exact cyclotomic polynomial."""
    n = int(order)
    if n <= 0:
        raise ValueError(n)
    divisors = [d for d in range(1, n + 1) if n % d == 0]
    built: dict[int, tuple[int, ...]] = {}
    for current in divisors:
        poly = (-1,) + (0,) * (current - 1) + (1,)
        for d in divisors:
            if d >= current:
                break
            if current % d:
                continue
            quotient = polynomial_divide_exact(poly, built[d])
            if quotient is None:
                raise AssertionError((current, d, poly))
            poly = quotient
        built[current] = poly
    return built[n]


@cache
def cyclotomic_power_coefficients(order: int, power: int) -> tuple[int, ...]:
    """Return exact LSF coefficients of ``Phi_order(z)**power``."""
    order, power = int(order), int(power)
    if order <= 0 or power <= 0:
        raise ValueError((order, power))
    return polynomial_power(cyclotomic_coefficients(order), power)


def polynomial_divisible_by_cyclotomic(
    coefficients: tuple[int, ...], order: int
) -> bool:
    """Exact integer-polynomial divisibility test by ``Phi_order``."""
    return (
        polynomial_divide_exact(
            tuple(map(int, coefficients)), cyclotomic_coefficients(int(order))
        )
        is not None
    )


def cyclotomic_value(order: int, value: int) -> int:
    """Return the exact integer evaluation ``Phi_order(value)``."""
    return evaluate_polynomial(cyclotomic_coefficients(int(order)), int(value))


def cyclotomic_one_plus_norm(order: int) -> int:
    """Return ``abs(Phi_order(-1))``.

    This is the algebraic norm of ``1+zeta_order`` up to sign.  The exact
    classification is useful for deciding which cyclotomic channels can gain
    2-adic valuation under reverse-add growth.
    """
    n = int(order)
    if n <= 0:
        raise ValueError(n)
    if n == 1:
        return 2
    if n == 2:
        return 0
    if is_power_of_two(n):
        return 2
    if n % 2 == 0:
        half = n // 2
        if half & 1:
            p = _prime_power_base(half)
            return p if p is not None else 1
    return 1


def cyclotomic_two_adic_growth_channel(order: int) -> str:
    """Classify the ``1+z`` action at the prime 2 for one cyclotomic order."""
    n = int(order)
    norm = cyclotomic_one_plus_norm(n)
    if n == 2:
        return "zero"
    if norm % 2 == 0:
        return "ramified"
    return "unit"


__all__ = [
    "cyclotomic_coefficients",
    "cyclotomic_one_plus_norm",
    "cyclotomic_power_coefficients",
    "cyclotomic_two_adic_growth_channel",
    "cyclotomic_value",
    "is_power_of_two",
    "polynomial_divisible_by_cyclotomic",
]
