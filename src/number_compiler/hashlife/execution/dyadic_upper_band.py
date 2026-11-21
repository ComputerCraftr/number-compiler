"""Project certified lower dyadic effects to upper affine responses."""

from __future__ import annotations

from number_compiler.arithmetic.automata.affine_port_action import AffinePortAction
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSupportRecord,
)


def certified_lower_upper_action(
    lower: DyadicReturnSupportRecord,
    lower_bits: int,
    *,
    cut: int,
    demand_width: int,
) -> AffinePortAction:
    """Project a lower effect after checking its exact aligned cylinder.

    The returned action is a value response. The caller retains the original
    lower support, including source guard and ordered safety information.
    """
    if type(lower) is not DyadicReturnSupportRecord:
        raise TypeError("upper band requires a certified lower support")
    width = lower.width
    if (
        type(lower_bits) is not int
        or type(cut) is not int
        or type(demand_width) is not int
        or width <= 0
        or cut < width
        or demand_width <= 0
        or not 0 <= lower_bits < (1 << cut)
        or lower.transfer.lower != (1 << width)
        or lower.transfer.upper < 0
        or (lower_bits & ((1 << width) - 1)) != lower.residue
    ):
        raise ValueError("upper band lacks its aligned lower cylinder")
    numerator = lower.transfer.upper * lower_bits + lower.transfer.offset
    if numerator % (1 << width):
        raise ArithmeticError("lower block lost its exact dyadic endpoint")
    return AffinePortAction.reduced(
        1 << demand_width, lower.transfer.upper, numerator >> cut
    )
