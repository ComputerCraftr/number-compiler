"""Small explicit Fermat-source oracle for validation only.

Production keeps the pumped radial/unit descriptor symbolic. This helper
checks small demands against the defining integer power without sharing the
production unit-seed or radial-lane arithmetic.
"""

from __future__ import annotations

from number_compiler.sequences.power_numbers.fermat_pumped_radial_unit import (
    MAX_EXPLICIT_WIDTH,
    MAX_SOURCE_PARAMETER_BITS,
    FermatPumpedRadialUnit,
    PumpedSourceBudgetExceeded,
)


def literal_pumped_fermat_remainder(
    source: FermatPumpedRadialUnit,
    *,
    max_width: int = 4_096,
    max_level: int = 4_096,
) -> int:
    """Evaluate ``3**(2**level) mod (2**(2**index)+1)`` for small checks."""
    if type(source) is not FermatPumpedRadialUnit:
        raise TypeError("expected an exact pumped Fermat source descriptor")
    if (
        type(max_width) is not int
        or not 2 <= max_width <= MAX_EXPLICIT_WIDTH
        or type(max_level) is not int
        or not 0 <= max_level <= MAX_SOURCE_PARAMETER_BITS
    ):
        raise PumpedSourceBudgetExceeded(("oracle-budgets", max_width, max_level))
    if source.width_extent > max_width:
        raise PumpedSourceBudgetExceeded("oracle width budget exceeded")
    if source.level > max_level:
        raise PumpedSourceBudgetExceeded("oracle level budget exceeded")
    width = source.width_extent.materialize(max_power=max_width.bit_length())
    modulus = (1 << width) + 1
    return pow(3, 1 << source.level, modulus)


__all__ = ["literal_pumped_fermat_remainder"]
