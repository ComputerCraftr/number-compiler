"""Positive-root arithmetic using the shared exact rational coefficient owner.

An element denotes sqrt(square); addition here is root-sum, not ordinary
addition of real square roots. This coordinate change does not identify ordered
source branches or certify a temporal/safety quotient.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.consumer_pullback import (
    ONE,
    ZERO,
    ExactRational,
)


@dataclass(frozen=True, slots=True)
class RootSemifieldElement:
    """A nonnegative radicand, with partial subtraction and nonzero division."""

    square: ExactRational

    def __init__(self, square: int | ExactRational = 0) -> None:
        if type(square) is int:
            value = ExactRational(square)
        elif type(square) is ExactRational:
            square.validate()
            value = square
        else:
            raise TypeError("root amplitude requires an exact rational or integer")
        if value < ZERO:
            raise ValueError("root squared amplitude must be nonnegative")
        object.__setattr__(self, "square", value)

    @classmethod
    def zero(cls) -> RootSemifieldElement:
        return cls(ZERO)

    @classmethod
    def one(cls) -> RootSemifieldElement:
        return cls(ONE)

    @property
    def is_zero(self) -> bool:
        return self.square == ZERO

    def _require(self, other: RootSemifieldElement) -> None:
        if type(other) is not RootSemifieldElement:
            raise TypeError("root operations require another root element")
        self.square.validate()
        other.square.validate()
        if self.square < ZERO or other.square < ZERO:
            raise ValueError("root squared amplitude must be nonnegative")

    def root_sum(self, other: RootSemifieldElement) -> RootSemifieldElement:
        self._require(other)
        return RootSemifieldElement(self.square + other.square)

    def root_difference(self, other: RootSemifieldElement) -> RootSemifieldElement:
        self._require(other)
        if self.square < other.square:
            raise ValueError("root difference requires a nonnegative remainder")
        return RootSemifieldElement(self.square - other.square)

    def multiply(self, other: RootSemifieldElement) -> RootSemifieldElement:
        self._require(other)
        return RootSemifieldElement(self.square * other.square)

    def reciprocal(self) -> RootSemifieldElement:
        self._require(self)
        if self.is_zero:
            raise ZeroDivisionError("zero root has no multiplicative inverse")
        return RootSemifieldElement(ONE / self.square)

    def divide(self, other: RootSemifieldElement) -> RootSemifieldElement:
        self._require(other)
        return self.multiply(other.reciprocal())

    def tropical_min(self, other: RootSemifieldElement) -> RootSemifieldElement:
        self._require(other)
        return self if self.square <= other.square else other

    def power(self, exponent: int) -> RootSemifieldElement:
        if type(exponent) is not int or exponent < 0:
            raise ValueError("root power requires a natural exponent")
        self._require(self)
        return RootSemifieldElement(
            ExactRational(
                pow(self.square.numerator, exponent),
                pow(self.square.denominator, exponent),
            )
        )
