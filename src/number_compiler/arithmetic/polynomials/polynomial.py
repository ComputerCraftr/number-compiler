"""Canonical exact integer-polynomial arithmetic for theorem/ring layers.

All polynomials are least-significant-coefficient first.  This module owns the
unmetered symbolic polynomial primitives used by cyclotomic construction,
finite quotient rings, special-number theorem coordinates, and reverse-add
real-cyclotomic relations.  Charged digit convolution remains deliberately in
``digit_convolution`` because its sparse/Karatsuba work metrics are part of a
different execution contract.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from number_compiler.arithmetic.fields.morphism_core import (
    BinaryPowerResult,
    binary_power,
)


def trim_polynomial(coefficients: Sequence[int]) -> tuple[int, ...]:
    out = list(map(int, coefficients)) or [0]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def polynomial_add_constant(coefficients: Sequence[int], delta: int) -> tuple[int, ...]:
    out = list(trim_polynomial(coefficients))
    out[0] += int(delta)
    return trim_polynomial(out)


def polynomial_multiply(first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
    """Return the exact LSF integer-polynomial product.

    This is the single unmodded polynomial multiplication primitive for the
    theorem/projection layer.  Do not duplicate it in cyclotomic or special
    family modules.
    """
    a = tuple(map(int, first))
    b = tuple(map(int, second))
    if not a or not b:
        return (0,)
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            if y:
                out[i + j] += x * y
    return trim_polynomial(out)


def polynomial_affine(
    source: Sequence[int],
    multiplier: Sequence[int],
    addend: Sequence[int],
) -> tuple[int, ...]:
    """Return ``multiplier*source + addend`` as one exact polynomial.

    Family modules use this when they need the unreduced raw coefficient field
    for normalization.  Quotient-ring execution uses the same multiplier and
    addend through :class:`AffineCocycle`/``CyclotomicAffineMorphism``.
    """
    product = list(polynomial_multiply(source, multiplier))
    bias = tuple(map(int, addend))
    if len(product) < len(bias):
        product.extend([0] * (len(bias) - len(product)))
    for i, value in enumerate(bias):
        product[i] += value
    return trim_polynomial(product)


def polynomial_square(coefficients: Sequence[int]) -> tuple[int, ...]:
    """Square through the canonical polynomial multiplication primitive."""
    values = trim_polynomial(coefficients)
    return polynomial_multiply(values, values)


def polynomial_power(coefficients: Sequence[int], exponent: int) -> tuple[int, ...]:
    exponent = int(exponent)
    if exponent < 0:
        raise ValueError(exponent)
    base = trim_polynomial(coefficients)
    return binary_power(
        base, exponent, identity=(1,), compose=polynomial_multiply
    ).value


def polynomial_remainder_monic(
    coefficients: Sequence[int], divisor: Sequence[int], *, modulus: int
) -> tuple[int, ...]:
    """Reduce modulo a monic polynomial and a coefficient modulus.

    Monicity makes this valid over non-fields such as ``Z/2**k``.  The result
    is padded to exactly ``degree(divisor)`` coefficients, giving one canonical
    quotient-ring coordinate.
    """
    modulus = int(modulus)
    div = trim_polynomial(divisor)
    if modulus <= 1 or not div or div[-1] != 1:
        raise ValueError((divisor, modulus))
    degree = len(div) - 1
    if degree <= 0:
        return ()
    a = [int(x) % modulus for x in coefficients] or [0]
    while len(a) > degree:
        coefficient = a[-1] % modulus
        shift = len(a) - len(div)
        if coefficient:
            for i, value in enumerate(div):
                a[shift + i] = (a[shift + i] - coefficient * value) % modulus
        a.pop()
    a += [0] * (degree - len(a))
    return tuple(value % modulus for value in a[:degree])


@dataclass(frozen=True, slots=True)
class MonicPolynomialRing:
    """Finite coefficient ring modulo one monic polynomial."""

    divisor: tuple[int, ...]
    modulus: int

    def __post_init__(self) -> None:
        divisor = trim_polynomial(self.divisor)
        modulus = int(self.modulus)
        if modulus <= 1 or len(divisor) <= 1 or divisor[-1] != 1:
            raise ValueError((divisor, modulus))
        object.__setattr__(self, "divisor", divisor)
        object.__setattr__(self, "modulus", modulus)

    @property
    def degree(self) -> int:
        return len(self.divisor) - 1

    @property
    def zero(self) -> tuple[int, ...]:
        return (0,) * self.degree

    @property
    def one(self) -> tuple[int, ...]:
        return (1,) + (0,) * (self.degree - 1)

    def reduce(self, coefficients: Sequence[int]) -> tuple[int, ...]:
        return polynomial_remainder_monic(
            coefficients, self.divisor, modulus=self.modulus
        )

    def add(self, first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
        a = tuple(first)
        b = tuple(second)
        if len(a) != self.degree or len(b) != self.degree:
            raise ValueError((len(a), len(b), self.degree))
        return tuple(
            (int(x) + int(y)) % self.modulus for x, y in zip(a, b, strict=True)
        )

    def subtract(self, first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
        a = tuple(first)
        b = tuple(second)
        if len(a) != self.degree or len(b) != self.degree:
            raise ValueError((len(a), len(b), self.degree))
        return tuple(
            (int(x) - int(y)) % self.modulus for x, y in zip(a, b, strict=True)
        )

    def scale(self, residue: Sequence[int], scalar: int) -> tuple[int, ...]:
        values = tuple(residue)
        if len(values) != self.degree:
            raise ValueError((len(values), self.degree))
        return tuple(int(scalar) * int(value) % self.modulus for value in values)

    def multiply(self, first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
        return self.reduce(polynomial_multiply(first, second))

    def square(self, residue: Sequence[int]) -> tuple[int, ...]:
        values = tuple(residue)
        return self.multiply(values, values)

    def power(
        self, residue: Sequence[int], exponent: int
    ) -> BinaryPowerResult[tuple[int, ...]]:
        values = self.reduce(residue)
        return binary_power(values, exponent, identity=self.one, compose=self.multiply)


def polynomial_divide_exact(
    numerator: Sequence[int], denominator: Sequence[int]
) -> tuple[int, ...] | None:
    """Divide integer polynomials exactly, returning ``None`` on remainder."""
    a = list(trim_polynomial(numerator))
    b = trim_polynomial(denominator)
    if not b or b[-1] != 1:
        raise ValueError("denominator must be monic")
    if len(a) < len(b):
        return None
    q = [0] * (len(a) - len(b) + 1)
    while len(a) >= len(b):
        coefficient = a[-1]
        shift = len(a) - len(b)
        q[shift] = coefficient
        if coefficient:
            for i, value in enumerate(b):
                a[shift + i] -= coefficient * value
        a = list(trim_polynomial(a))
    if any(a):
        return None
    return trim_polynomial(q)


def evaluate_polynomial(coefficients: Sequence[int], value: int) -> int:
    x = int(value)
    out = 0
    for coefficient in reversed(tuple(map(int, coefficients))):
        out = out * x + coefficient
    return out


def trace_square_polynomial(coefficients: Sequence[int]) -> tuple[int, ...]:
    """Polynomial lift of the universal trace square ``u -> u**2 - 2``."""
    return polynomial_add_constant(polynomial_square(coefficients), -2)


__all__ = [
    "trim_polynomial",
    "polynomial_add_constant",
    "polynomial_multiply",
    "polynomial_affine",
    "MonicPolynomialRing",
    "polynomial_square",
    "polynomial_power",
    "polynomial_remainder_monic",
    "polynomial_divide_exact",
    "evaluate_polynomial",
    "trace_square_polynomial",
]
