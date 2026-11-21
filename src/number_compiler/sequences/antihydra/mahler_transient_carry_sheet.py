"""Source-free eight-step carry/Bellman atoms for transient Antihydra leaves.

Only the final 256 source-cylinder summaries are cached. The two-child lift
preserves the physical H map, H -> floor(3H/2), and the ordered prefix minimum.
No source occurrence, parity word, or intermediate level is retained.
"""

from __future__ import annotations

from functools import lru_cache

LEAF_BITS = 8
LEAF_GAIN = 3**LEAF_BITS


def physical_two_child_summary(
    width: int,
    correction: int,
    delta: int,
    minimum: int,
    odd: int,
    parity: int,
) -> tuple[tuple[int, int, int, int], tuple[int, int, int, int]]:
    """Return lower and upper children using one authenticated parent action."""
    if (
        any(
            type(x) is not int for x in (width, correction, delta, minimum, odd, parity)
        )
        or width < 0
        or correction < 0
        or odd < 0
        or parity not in (0, 1)
    ):
        raise ValueError("invalid physical two-child summary")
    span = 1 << width

    def child(p: int) -> tuple[int, int, int, int]:
        new_delta = delta + 2 - 3 * p
        return 3 * correction + span * p, new_delta, min(minimum, new_delta), odd + p

    return child(parity), child(1 - parity)


@lru_cache(maxsize=1)
def eight_step_carry_sheet() -> tuple[tuple[int, int, int, int], ...]:
    """Build 256 exact cylinder atoms once, freeing every intermediate row."""
    row: tuple[tuple[int, int, int, int], ...] = ((0, 0, 0, 0),)
    gain = 1
    for width in range(LEAF_BITS):
        modulus = 1 << width
        next_row: list[tuple[int, int, int, int] | None] = [None] * (2 * modulus)
        for residue, (correction, delta, minimum, odd) in enumerate(row):
            numerator = gain * residue - correction
            if numerator < 0 or numerator % modulus:
                raise ArithmeticError("carry sheet lost its source guard")
            parity = (numerator // modulus) & 1
            next_row[residue], next_row[residue + modulus] = physical_two_child_summary(
                width, correction, delta, minimum, odd, parity
            )
        row = tuple(x for x in next_row if x is not None)
        gain *= 3
    if len(row) != 256:
        raise ArithmeticError("eight-step carry sheet has an incomplete last row")
    return row
