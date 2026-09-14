"""Exact multiplicative divisor observations, with no factor-table dependency.

Saturation loses overflow; meet is gcd, not arithmetic addition. Observing a
sum requires its residue because equal valuations can cancel. Outputs remain
queries on an action and are never used as temporal identities.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, lcm

from number_compiler.arithmetic.fields.radix import bit_width


@dataclass(frozen=True, slots=True)
class TropicalDivisorState:
    """Factor-free bounded valuation vector encoded as one divisor of N."""

    modulus: int
    divisor: int

    def __post_init__(self) -> None:
        modulus, divisor = int(self.modulus), int(self.divisor)
        if modulus < 2 or divisor < 1 or modulus % divisor:
            raise ValueError((modulus, divisor))
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "divisor", divisor)

    @classmethod
    def one(cls, modulus: int) -> TropicalDivisorState:
        return cls(int(modulus), 1)

    @classmethod
    def zero(cls, modulus: int) -> TropicalDivisorState:
        return cls(int(modulus), int(modulus))

    @classmethod
    def observe(cls, modulus: int, value: int) -> TropicalDivisorState:
        modulus = int(modulus)
        return cls(modulus, gcd(modulus, int(value)))

    def _check(self, other: TropicalDivisorState) -> None:
        if not isinstance(other, TropicalDivisorState) or self.modulus != other.modulus:
            raise ValueError((self, other))

    def multiply(self, other: TropicalDivisorState) -> TropicalDivisorState:
        """Saturated tropical addition of all hidden local valuations."""
        self._check(other)
        return TropicalDivisorState(
            self.modulus,
            gcd(self.modulus, self.divisor * other.divisor),
        )

    def meet(self, other: TropicalDivisorState) -> TropicalDivisorState:
        """Componentwise valuation minimum."""
        self._check(other)
        return TropicalDivisorState(self.modulus, gcd(self.divisor, other.divisor))

    def join(self, other: TropicalDivisorState) -> TropicalDivisorState:
        """Componentwise valuation maximum."""
        self._check(other)
        return TropicalDivisorState(self.modulus, lcm(self.divisor, other.divisor))

    def local_height(self, prime: int, exponent: int) -> int:
        prime, exponent = int(prime), int(exponent)
        if prime < 2 or exponent < 1 or self.modulus % (prime**exponent):
            raise ValueError((prime, exponent, self.modulus))
        value, height = self.divisor, 0
        while height < exponent and value % prime == 0:
            value //= prime
            height += 1
        return height

    @property
    def proper_factor(self) -> int | None:
        return self.divisor if 1 < self.divisor < self.modulus else None

    @property
    def description_bits(self) -> int:
        return bit_width(self.modulus) + bit_width(self.divisor)
