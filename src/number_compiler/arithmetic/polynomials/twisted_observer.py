"""Demanded signed cylinder projections and compatible arithmetic support.

A nonzero sheet certifies a nonzero polynomial. A zero finite sheet alone does
not certify polynomial zero. Evaluation commutes only at a compatible modulus.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.tropical_divisor import TropicalDivisorState
from number_compiler.arithmetic.polynomials.digit_convolution import (
    fold_cyclic,
    fold_negacyclic,
)


@dataclass(frozen=True, slots=True)
class TwistedCylinderProjection:
    width: int
    sign: int
    coefficients: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.width) is not int or self.width < 1:
            raise ValueError("positive cylinder width required")
        if type(self.sign) is not int or self.sign not in (-1, 1):
            raise ValueError("twist must be +/-1")
        if len(self.coefficients) != self.width or any(
            type(v) is not int for v in self.coefficients
        ):
            raise ValueError("expected an exact coefficient for each cylinder position")

    @classmethod
    def observe(
        cls, coefficients: Iterable[int], *, width: int, sign: int
    ) -> TwistedCylinderProjection:
        if (
            type(width) is not int
            or width < 1
            or type(sign) is not int
            or sign not in (-1, 1)
        ):
            raise ValueError("invalid twisted cylinder")
        fold = fold_cyclic if sign == 1 else fold_negacyclic
        return cls(width, sign, fold(coefficients, width))

    def append(
        self, after: TwistedCylinderProjection, *, span: int
    ) -> TwistedCylinderProjection:
        """Observe concatenation: self + z**span * after in the same sheet."""
        if type(span) is not int or span < 0:
            raise ValueError("word span must be a nonnegative exact integer")
        if (self.width, self.sign) != (after.width, after.sign):
            raise ValueError("concatenation requires the same cylinder sheet")
        values = list(self.coefficients)
        for i, coefficient in enumerate(after.coefficients):
            turns, slot = divmod(span + i, self.width)
            values[slot] += (
                -coefficient if self.sign == -1 and turns & 1 else coefficient
            )
        return TwistedCylinderProjection(self.width, self.sign, tuple(values))

    @property
    def nonzero(self) -> bool:
        return any(self.coefficients)

    def support(
        self, *, radix: int, modulus: int, constant: int = 0
    ) -> TropicalDivisorState:
        if (
            type(radix) is not int
            or type(modulus) is not int
            or type(constant) is not int
            or modulus < 2
        ):
            raise ValueError("exact radix and modulus greater than one required")
        if pow(radix, self.width, modulus) != self.sign % modulus:
            raise ValueError(
                "evaluation modulus is incompatible with the cylinder twist"
            )
        residue = 0
        for coefficient in reversed(self.coefficients):
            residue = (residue * radix + coefficient) % modulus
        return TropicalDivisorState.observe(modulus, residue + constant)


def first_mirror_obstruction(
    width: int,
    digit: Callable[[int], int],
    *,
    first_width: int = 1,
) -> TwistedCylinderProjection | None:
    """First nonzero sheet of the mirror defect; None certifies this target only.

    Queries cyclic d, then negacyclic d,2d,4d,... . The target digits are read once and
    the shared mirror defect is folded for each demanded sheet. This is an optional certificate query;
    the ordinary early mirrored-digit comparison remains the cheaper default.
    No exact integer or temporal history is constructed here.
    """
    if (
        type(width) is not int
        or width < 1
        or type(first_width) is not int
        or first_width < 1
    ):
        raise ValueError("positive target and first-sheet widths required")
    # Read each target digit once across all sheets. Keep the mirror defect,
    # not an exact integer or a temporal history.
    difference = [0] * width
    for i in range(width // 2):
        delta = digit(i) - digit(width - 1 - i)
        difference[i] = delta
        difference[width - 1 - i] = -delta
    sheet, sign = first_width, 1
    while True:
        projection = TwistedCylinderProjection.observe(
            difference,
            width=sheet,
            sign=sign,
        )
        if projection.nonzero:
            return projection
        # Degree below sheet: this individual zero remainder is the zero polynomial.
        if sheet >= width:
            return None
        if sign == 1:
            sign = -1
        else:
            sheet *= 2
