"""Cheap pointed admission hints for the bounded conditional scheduler.

The checks in this module can only reject a probe or suggest its exact
physical horizon. They never issue a source guard or authorize an action; the
conditional return compiler remains responsible for whole-cylinder proof.
"""

from __future__ import annotations

from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.border_harmonic_ring import (
    zero_tail_word_coefficients,
)


def _pointed_repeated_motif_ticks(
    source: int, exponent: int, max_tail: int
) -> int | None:
    """Return a necessary pointed match for a supported repeated motif.

    At most eight actual 6305 returns are inspected. The final divisibility
    is necessary for the source-closed powered parity action, but cannot
    replace its guard pullbacks or certify other points in a cylinder.
    """
    copies = 1 << exponent
    upper = 3 * ((source - 3) // 10) + 1
    tails: list[int] = []
    physical = 0
    for length in range(1, min(8, copies) + 1):
        tail = v2_positive(upper)
        if tail > max_tail:
            break
        odd = upper >> tail
        if odd & 3 != 3:
            break
        upper = (9 * odd + 1) >> 2
        tails.append(tail)
        physical += tail + 4
        if length not in (1, 2, 4, 8):
            continue
        gain, offset, steps = zero_tail_word_coefficients(tuple(tails))
        repeats = copies // length
        needed = steps * repeats
        defect = ((1 << steps) - gain) * source - offset
        if defect % (1 << needed) == 0:
            return physical * repeats
    return None


def find_bounded_conditional_driver(
    source: int, remaining: int, max_tail: int = 12
) -> tuple[int, int] | None:
    """Suggest the largest supported power fitting this pointed horizon.

    This filter is intentionally narrow and non-authoritative. A positive
    result must still pass the conditional compiler's whole-fiber admission.
    """
    if (
        type(source) is not int
        or source <= 0
        or type(remaining) is not int
        or remaining < 256
        or type(max_tail) is not int
        or not 1 <= max_tail <= 64
        or source % 10 != 3
        or source.bit_length() < 256
    ):
        return None
    largest = min(7, (remaining // 4).bit_length() - 1)
    for exponent in range(largest, 4, -1):
        ticks = _pointed_repeated_motif_ticks(source, exponent, max_tail)
        if ticks is not None and ticks <= remaining and 2 * ticks >= remaining:
            return exponent, ticks
    return None


__all__ = ("find_bounded_conditional_driver",)
