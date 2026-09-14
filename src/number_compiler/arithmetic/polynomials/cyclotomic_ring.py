"""Canonical finite cyclotomic quotient-ring arithmetic.

``CyclotomicRing`` is the shared algebra object behind source-digit blocks,
affine morphisms, prime wheel observers, Fermat/Mersenne square projections,
and reverse-add/Collatz cyclotomic coordinates.  It owns module identity and
all multiply/reduce/power operations so family modules cannot grow private
quotient-ring multiplication kernels.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, field

from number_compiler.arithmetic.fields.morphism_core import BinaryPowerResult
from number_compiler.arithmetic.polynomials.cyclotomic import (
    cyclotomic_power_coefficients,
)
from number_compiler.arithmetic.polynomials.polynomial import MonicPolynomialRing


@dataclass(frozen=True, slots=True)
class CyclotomicRing:
    order: int
    modulus: int
    power: int = 1
    factor: tuple[int, ...] | None = None
    _quotient: MonicPolynomialRing = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        order = int(self.order)
        modulus = int(self.modulus)
        power = int(self.power)
        factor = (
            None
            if self.factor is None
            else tuple(int(v) % modulus for v in self.factor)
        )
        if order <= 0 or modulus <= 1 or power <= 0:
            raise ValueError(self)
        if factor is not None and (
            power != 1 or len(factor) <= 1 or factor[-1] % modulus != 1
        ):
            raise ValueError((order, modulus, power, factor))
        divisor = factor or cyclotomic_power_coefficients(order, power)
        if len(divisor) <= 1 or divisor[-1] != 1:
            raise ValueError((order, modulus, power, factor, divisor))
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "power", power)
        object.__setattr__(self, "factor", factor)
        object.__setattr__(
            self, "_quotient", MonicPolynomialRing(tuple(divisor), modulus)
        )

    @property
    def divisor(self) -> tuple[int, ...]:
        return self.factor or cyclotomic_power_coefficients(self.order, self.power)

    @property
    def degree(self) -> int:
        return len(self.divisor) - 1

    @property
    def module_key(self) -> tuple[object, ...]:
        if self.factor is None:
            return ("cyclotomic-digit-module", self.order, self.power, self.modulus)
        return ("cyclotomic-digit-factor", self.order, self.modulus, self.factor)

    @property
    def quotient(self) -> MonicPolynomialRing:
        return self._quotient

    @property
    def zero(self) -> tuple[int, ...]:
        return self.quotient.zero

    @property
    def one(self) -> tuple[int, ...]:
        return self.quotient.one

    def reduce(self, coefficients: Sequence[int]) -> tuple[int, ...]:
        return self.quotient.reduce(coefficients)

    def add(self, first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
        return self.quotient.add(first, second)

    def subtract(self, first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
        return self.quotient.subtract(first, second)

    def scale(self, residue: Sequence[int], scalar: int) -> tuple[int, ...]:
        return self.quotient.scale(residue, scalar)

    def multiply(self, first: Sequence[int], second: Sequence[int]) -> tuple[int, ...]:
        return self.quotient.multiply(first, second)

    def square(self, residue: Sequence[int]) -> tuple[int, ...]:
        return self.quotient.square(residue)

    def power_residue(
        self, residue: Sequence[int], exponent: int
    ) -> BinaryPowerResult[tuple[int, ...]]:
        return self.quotient.power(residue, exponent)


__all__ = ["CyclotomicRing"]
