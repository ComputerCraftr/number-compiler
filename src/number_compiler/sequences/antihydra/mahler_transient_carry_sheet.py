"""Source-free eight-step carry/Bellman atoms for transient Antihydra leaves.

Only demanded bounded source-cylinder alphabets are cached (at most 510
summaries over widths 1 through 8). The two-child lift preserves
H -> floor(3H/2) and the ordered prefix minimum.
No source occurrence, parity word, or intermediate level is retained.
"""

from __future__ import annotations

from collections.abc import Callable
from functools import lru_cache

from number_compiler.arithmetic.fields.consumer_pullback import (
    compose_prefix_safety_values,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive

LEAF_BITS = 8
LEAF_GAIN = 3**LEAF_BITS


def physical_carry_at(steps: int, residue: int) -> tuple[int, int, int, int]:
    """Compute one bounded response without allocating its full alphabet."""
    if (
        type(steps) is not int
        or not 1 <= steps <= LEAF_BITS
        or type(residue) is not int
        or not 0 <= residue < 1 << steps
    ):
        raise ValueError("invalid physical carry response")
    value = residue
    correction = delta = minimum = odd = 0
    for position in range(steps):
        parity = value & 1
        correction = 3 * correction + (parity << position)
        value = (3 * value - parity) >> 1
        delta += 2 - 3 * parity
        minimum = min(minimum, delta)
        odd += parity
    return correction, delta, minimum, odd


def select_repeat_response(h: int, width: int) -> tuple[int, int, int, int, int] | None:
    """Select a bounded row for immediate use at this source seam."""
    for atom in (8, 4):
        if width < atom * 3:
            continue
        correction, delta, minimum, odd = physical_carry_at(atom, h & ((1 << atom) - 1))
        factor = 3**atom - (1 << atom)
        guard = (1 << (atom * 3)) - 1
        if not (factor * (h & guard) - correction) & guard:
            return atom, correction, delta, minimum, odd
    return None


def evaluate_repeat_response(
    h: int,
    width: int,
    selected: tuple[int, int, int, int, int],
    require_bits: Callable[[int], None],
) -> tuple[tuple[int, int, int, int, int], int]:
    """Fold the selected row; caller owns scratch and work accounting."""
    atom, correction, block_delta, block_minimum, block_odd = selected
    factor = 3**atom - (1 << atom)
    require_bits(8 * (h.bit_length() + 3 * atom + 16))
    defect = factor * h - correction
    length = width if defect == 0 else min(width, v2_positive(abs(defect)))
    repetitions, tail = divmod(length, atom)
    full_length = atom * repetitions
    require_bits(8 * (h.bit_length() + 3 * length + 64))
    upper = 3**full_length
    geometric, remainder = divmod(upper - (1 << full_length), factor)
    if remainder:
        raise ArithmeticError("repeat geometric factor is not integral")
    endpoint = h + geometric * (defect >> full_length)
    delta = repetitions * block_delta
    minimum = block_minimum + min(0, (repetitions - 1) * block_delta)
    odd_steps = repetitions * block_odd
    if tail:
        tail_k, tail_delta, tail_minimum, tail_odd = physical_carry_at(
            tail, h & ((1 << tail) - 1)
        )
        endpoint = (3**tail * endpoint - tail_k) >> tail
        delta, minimum = compose_prefix_safety_values(
            delta, minimum, tail_delta, tail_minimum
        )
        odd_steps += tail_odd
    operand_bits = (
        h.bit_length()
        + defect.bit_length()
        + endpoint.bit_length()
        + upper.bit_length()
        + length
    )
    return (length, delta, minimum, odd_steps, endpoint - 1), operand_bits


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


@lru_cache(maxsize=LEAF_BITS)
def physical_carry_sheet(steps: int) -> tuple[tuple[int, int, int, int], ...]:
    """The complete fixed-width response alphabet, with no pointed source."""
    if type(steps) is not int or not 1 <= steps <= LEAF_BITS:
        raise ValueError("physical carry sheet exceeds its finite alphabet")
    row: tuple[tuple[int, int, int, int], ...] = ((0, 0, 0, 0),)
    gain = 1
    for width in range(steps):
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
    if len(row) != 1 << steps:
        raise ArithmeticError("physical carry sheet has an incomplete last row")
    return row
