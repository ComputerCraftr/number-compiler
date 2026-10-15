"""Exact binary width of nonnegative affine source views without endpoint output."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


def nonnegative_affine_width(
    source: int,
    shift: int,
    multiplier: int,
    offset: int,
    ledger: ResourceLedger,
) -> int:
    """Return ``(multiplier * (source >> shift) + offset).bit_length()``.

    Leading-bit intervals usually settle the width without multiplying the
    whole source. Ambiguous exact boundaries refine to full source precision;
    no logarithm or approximate comparison authorizes an output width.
    """
    if any(type(value) is not int for value in (source, shift, multiplier, offset)):
        raise TypeError("affine width requires exact integer coordinates")
    if min(source, shift, multiplier, offset) < 0:
        raise ValueError("affine width requires nonnegative coordinates")
    if type(ledger) is not ResourceLedger:
        raise TypeError("affine width requires a resource ledger")
    ledger.bump(_fields_keys.AFFINE_WIDTH_REQUESTS)
    for suffix in (
        "operand_bits",
        "interval_checks",
        "refinements",
        "exact_boundaries",
        "failures",
    ):
        ledger.bump("affine_width_" + suffix, 0)
    width = max(0, source.bit_length() - shift)
    if width == 0 or multiplier == 0:
        return offset.bit_length()
    precision = min(width, 16)
    owner = ledger.register("affine-width-scratch", "execution_stack")
    while True:
        bits = precision + multiplier.bit_length() + offset.bit_length() + 64
        ledger.bump(_fields_keys.AFFINE_WIDTH_OPERAND_BITS, bits)
        try:
            with ledger.reservation(owner, nodes=8 * ((bits + 63) // 64)):
                lower_width, upper_width = _width_interval(
                    source, shift, multiplier, offset, width, precision
                )
        except BaseException:
            ledger.bump(_fields_keys.AFFINE_WIDTH_FAILURES)
            raise
        ledger.bump(_fields_keys.AFFINE_WIDTH_INTERVAL_CHECKS)
        if precision == width:
            ledger.bump(_fields_keys.AFFINE_WIDTH_EXACT_BOUNDARIES)
        if lower_width == upper_width:
            return lower_width
        ledger.bump(_fields_keys.AFFINE_WIDTH_REFINEMENTS)
        precision = min(width, precision * 2)


def _width_interval(
    source: int, shift: int, multiplier: int, offset: int, width: int, precision: int
) -> tuple[int, int]:
    removed = width - precision
    prefix = source >> (shift + removed)
    # The projected source lies between these two consecutive prefixes.
    # Round the offset outwards at the same scale, never rounding a decision.
    offset_high = offset >> removed
    lower_high = multiplier * prefix + offset_high
    if removed == 0:
        exact = lower_high.bit_length()
        return exact, exact
    offset_remainder = offset != offset_high << removed
    upper_high = multiplier * (prefix + 1) + offset_high + int(offset_remainder)
    lower_width = 0 if lower_high == 0 else removed + lower_high.bit_length()
    # upper_high*2^removed is a strict upper bound. Its predecessor has this
    # width even when upper_high is a power of two.
    return lower_width, removed + (upper_high - 1).bit_length()
