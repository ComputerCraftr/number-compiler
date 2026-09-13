"""Demanded palindrome consumers; finite safety checks never certify future time."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot
from number_compiler.arithmetic.formula.types import RadixSpec


def mirror_palindrome(width: int, digit: Callable[[int], int]) -> bool:
    """Compare outer target pairs first, requesting no unneeded interior digits."""
    if type(width) is not int or width < 1:
        raise ValueError("target width must be a positive integer")
    for i in range(width // 2):
        if digit(i) != digit(width - 1 - i):
            return False
    return True


def next_result_is_palindrome(
    arena: FormulaArena, pair_root: FormulaRoot, spec: RadixSpec
) -> bool:
    """Exact next-result query on a symmetric reverse-add pair occurrence.

    Like next_digit_formula, this interface requires the actual symmetric pair
    field. It is an output query outside powered jumps, not a successor key.
    No growth plus any carry implies nonpalindrome; without carries the target
    equals the symmetric pair field. Growth compares the shifted TARGET mirror.
    """
    from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump
    from number_compiler.arithmetic.formula.summary import (
        get_summary,
        synthesize_symmetric_summary,
    )
    from number_compiler.sequences.reverse_add.digits import next_digit_formula

    forbid_in_powered_jump("next_result_is_palindrome")
    summary = get_summary(arena, pair_root, spec)
    if summary is None:
        summary = synthesize_symmetric_summary(arena, pair_root, spec)
    if not summary.growth_from_outer_symmetry:
        # Starting at zero, a real carry exists iff some pair value >= base.
        # Symmetry halves the demand, and there is no target construction.
        for i in range((pair_root.width + 1) // 2):
            value = sum(
                arena.eval_closed_bit(p, i) << bit
                for bit, p in enumerate(pair_root.planes)
            )
            if value >= spec.base:
                return False
        return True
    target = next_digit_formula(arena, pair_root, spec)

    def digit(position: int) -> int:
        return sum(
            arena.eval_closed_bit(p, position) << bit
            for bit, p in enumerate(target.planes)
        )

    return mirror_palindrome(target.width, digit)
