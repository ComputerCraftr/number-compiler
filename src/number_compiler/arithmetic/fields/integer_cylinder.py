"""Exact finite interval/coset geometry, independent of source authority.

Families authenticate the source and its action. This value algebra only
intersects their integer constraints and transports the complete resulting
progression; a harmonic projection must not replace its stride.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Self

from number_compiler.arithmetic.fields.integer_congruence import join_congruences


@dataclass(frozen=True, slots=True)
class IntegerCylinder:
    lower: int
    upper: int
    residue: int
    modulus: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.lower, self.upper, self.residue, self.modulus)
        ):
            raise TypeError("integer cylinder coordinates must be exact integers")
        if self.lower > self.upper or self.modulus < 1:
            raise ValueError(
                "integer cylinder requires ordered bounds and positive stride"
            )
        if not 0 <= self.residue < self.modulus:
            raise ValueError("integer cylinder residue must be canonical")
        if self.first > self.upper:
            raise ValueError("integer cylinder is empty")

    @property
    def first(self) -> int:
        return self.lower + (self.residue - self.lower) % self.modulus

    @property
    def last(self) -> int:
        return self.upper - (self.upper - self.residue) % self.modulus

    @property
    def count(self) -> int:
        return 1 + (self.last - self.first) // self.modulus

    def contains(self, value: int) -> bool:
        return (
            type(value) is int
            and self.lower <= value <= self.upper
            and value % self.modulus == self.residue
        )

    def intersect_interval(self, lower: int, upper: int) -> Self | None:
        if type(lower) is not int or type(upper) is not int:
            raise TypeError("interval bounds must be exact integers")
        if lower > upper:
            raise ValueError("interval bounds must be ordered")
        lo, hi = max(lower, self.lower), min(upper, self.upper)
        if lo > hi or lo + (self.residue - lo) % self.modulus > hi:
            return None
        return type(self)(lo, hi, self.residue, self.modulus)

    def intersect_congruence(self, residue: int, modulus: int) -> Self | None:
        if type(residue) is not int or type(modulus) is not int:
            raise TypeError("congruence coordinates must be exact integers")
        if modulus < 1:
            raise ValueError("congruence modulus must be positive")
        joined = join_congruences(
            (self.residue, self.modulus), (residue % modulus, modulus)
        )
        if joined is None:
            return None
        r, m = joined
        if self.lower + (r - self.lower) % m > self.upper:
            return None
        return type(self)(self.lower, self.upper, r, m)

    def affine_image(
        self,
        gain: int,
        offset: int = 0,
        denominator: int = 1,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> Self:
        """Image under an increasing integral affine map of the whole coset.

        Both the first numerator and stride must divide exactly. Even a
        singleton retains the requested coset's integral-stride obligation.
        This arithmetic check does not authenticate a family transition.
        If supplied, ``charge_bits`` receives the operand bits before any
        map validation or arithmetic, including requests that later refuse.
        """
        if any(type(value) is not int for value in (gain, offset, denominator)):
            raise TypeError("affine coordinates must be exact integers")
        if charge_bits is not None:
            charge_bits(
                sum(
                    value.bit_length()
                    for value in (
                        self.lower,
                        self.upper,
                        self.residue,
                        self.modulus,
                        gain,
                        offset,
                        denominator,
                    )
                )
            )
        if gain < 1 or denominator < 1:
            raise ValueError("affine gain and denominator must be positive")
        first_numerator = gain * self.first + offset
        stride_numerator = gain * self.modulus
        if first_numerator % denominator or stride_numerator % denominator:
            raise ValueError("affine map is not integral on the source coset")
        first = first_numerator // denominator
        last = (gain * self.last + offset) // denominator
        stride = stride_numerator // denominator
        return type(self)(first, last, first % stride, stride)

    def enumerated(self, limit: int = 64) -> tuple[int, ...] | None:
        """Bounded complete enumeration; None preserves an unresolved large fiber."""
        if type(limit) is not int or not 1 <= limit <= 4096:
            raise ValueError("integer fiber limit must be in 1..4096")
        count = self.count
        if count > limit:
            return None
        return tuple(self.first + index * self.modulus for index in range(count))
