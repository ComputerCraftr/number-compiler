"""Non-eager symbolic radial/unit source for Fermat's nested ``1+z`` fold.

For ``w=2**n`` in ``Z[z]/(z**w+1)``, the exact split
``(1+z)**w = 2 U_w`` gives
``(1+z)**(2**t) = 2**h U_w**h`` for ``h=2**(t-n)`` and ``t>=n``.
This object stores that identity as source metadata. It does not expand the
binomial row, evaluate the candidate residue, or issue a prime decision.

The powered 2-adic valuation and the unit coordinate are kept separate:
nilpotence of the raw row modulo ``2**b`` does not imply that the unit lane
vanishes. Numerical candidate-modulus evaluation lives only in test support.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent

MAX_SOURCE_PARAMETER_BITS = 4_096
MAX_EXPLICIT_WIDTH = 65_536


class PumpedSourceBudgetExceeded(ValueError):
    """An explicit coefficient or numerical audit exceeds its work budget."""


def _exact_positive(value: int, name: str) -> int:
    if type(value) is not int or value < 1:
        raise ValueError((name, value))
    if value.bit_length() > MAX_SOURCE_PARAMETER_BITS:
        raise PumpedSourceBudgetExceeded((name, "parameter-bit-budget"))
    return value


@dataclass(frozen=True, slots=True)
class FermatPumpedRadialUnit:
    """Compact exact source descriptor indexed by Fermat index and level."""

    index: int
    level: int

    def __post_init__(self) -> None:
        index = _exact_positive(self.index, "Fermat index")
        level = self.level
        if type(level) is not int or level < index:
            raise ValueError("nested source level must be an exact integer >= index")
        if level.bit_length() > MAX_SOURCE_PARAMETER_BITS:
            raise PumpedSourceBudgetExceeded(("level", "parameter-bit-budget"))

    @property
    def width_extent(self) -> DyadicExtent:
        """The negacyclic width ``2**index`` without lowering the shift."""
        return DyadicExtent(self.index)

    @property
    def radial_log2(self) -> int:
        """Return ``log2(h)`` for ``h=2**(level-index)``."""
        return self.level - self.index

    @property
    def is_terminal(self) -> bool:
        """Compare the level with ``2**index-1`` without materializing it."""
        return DyadicExtent(self.index, -1) == self.level

    def advance(self, delta: int) -> FermatPumpedRadialUnit:
        """Advance the nested source without constructing the power ``h``."""
        if type(delta) is not int or delta < 0:
            raise ValueError(delta)
        if delta.bit_length() > MAX_SOURCE_PARAMETER_BITS:
            raise PumpedSourceBudgetExceeded(("delta", "parameter-bit-budget"))
        return FermatPumpedRadialUnit(self.index, self.level + delta)

    def annihilated_at_precision(self, bits: int) -> bool:
        """Whether every raw coefficient is divisible by ``2**bits``."""
        if type(bits) is not int or bits < 1:
            raise ValueError(bits)
        return self.radial_log2 >= (bits - 1).bit_length()

    def coefficient_mod_power_of_two(self, position: int, *, bits: int) -> int:
        """Demand a raw coefficient only when the exact radial factor kills it."""
        if type(position) is not int or not self.width_extent.contains_index(position):
            raise IndexError(position)
        if self.annihilated_at_precision(bits):
            return 0
        raise PumpedSourceBudgetExceeded(
            "raw source is live at this precision; the unit lane is still required"
        )

    def seed_coefficient(self, position: int, *, max_width: int = 4_096) -> int:
        """Demand one coefficient of ``U_w`` under a preflighted width cap."""
        if type(max_width) is not int or not 2 <= max_width <= MAX_EXPLICIT_WIDTH:
            raise PumpedSourceBudgetExceeded(("explicit-width-budget", max_width))
        if type(position) is not int or not self.width_extent.contains_index(position):
            raise IndexError(position)
        if self.width_extent > max_width:
            raise PumpedSourceBudgetExceeded(
                "requested binomial seed exceeds width budget"
            )
        if position == 0:
            return 0
        width = self.width_extent.materialize(max_power=max_width.bit_length())
        return comb(width, position) // 2

    def scale_modulus_symbol(self) -> tuple[str, int | None]:
        """Describe ``2**h`` modulo ``F_n`` without constructing ``h`` or ``F_n``."""
        exponent_power = self.radial_log2
        if exponent_power > self.index:
            return ("ONE", 1)
        if exponent_power == self.index:
            return ("MINUS_ONE", -1)
        return ("POWER_OF_TWO", exponent_power)


__all__ = [
    "MAX_EXPLICIT_WIDTH",
    "MAX_SOURCE_PARAMETER_BITS",
    "FermatPumpedRadialUnit",
    "PumpedSourceBudgetExceeded",
]
