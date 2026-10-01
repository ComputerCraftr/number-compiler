"""Demanded palindrome consumers; finite safety checks never certify future time."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator
from contextlib import contextmanager

from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
    first_mirror_obstruction,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList


def mirror_palindrome(width: int, digit: Callable[[int], int]) -> bool:
    """Compare outer target pairs first, requesting no unneeded interior digits."""
    if type(width) is not int or width < 1:
        raise ValueError("target width must be a positive integer")
    for i in range(width // 2):
        if digit(i) != digit(width - 1 - i):
            return False
    return True


@contextmanager
def _completed_output_buffer(
    width: int,
    digits: Iterable[int],
    *,
    ledger: ResourceLedger,
    scratch: LedgerList[int],
) -> Iterator[LedgerList[int]]:
    """Reserve and release one complete output for mirrored-coordinate queries.

    Powered output is supplied in least-significant-first order. Its transient
    buffer and the shared observer's defect scratch are reserved before the
    stream is consumed, so mirrored positions need no temporal point queries.
    """
    if type(width) is not int or width < 1:
        raise ValueError("positive target width required")
    if type(ledger) is not ResourceLedger or type(scratch) is not LedgerList:
        raise TypeError("mirror output requires a ledger-owned scratch list")
    if (
        scratch.ledger is not ledger
        or scratch.append_only
        or scratch.nodes_per_entry != 2
    ):
        raise ValueError("mirror output scratch belongs to another ledger or policy")
    if scratch:
        raise RuntimeError("mirror output scratch is already in use")
    with ledger.reservation(scratch.owner, entries=width, nodes=2 * width):
        try:
            for digit in digits:
                if len(scratch) >= width:
                    raise ValueError("completed output stream exceeds its width")
                scratch.append(digit)
            if len(scratch) != width:
                raise ValueError("completed output stream width mismatch")
            yield scratch
        finally:
            scratch.clear()


def mirror_obstruction_from_output(
    width: int,
    digits: Iterable[int],
    *,
    ledger: ResourceLedger,
    scratch: LedgerList[int],
    first_width: int = 1,
) -> TwistedCylinderProjection | None:
    """Compute the exact obstruction from a single completed output stream."""
    if type(first_width) is not int or first_width < 1:
        raise ValueError("positive first-sheet width required")
    with _completed_output_buffer(width, digits, ledger=ledger, scratch=scratch):
        return first_mirror_obstruction(
            width, scratch.__getitem__, first_width=first_width
        )


def mirror_palindrome_from_output(
    width: int,
    digits: Iterable[int],
    *,
    ledger: ResourceLedger,
    scratch: LedgerList[int],
) -> bool:
    """Avoid repeated temporal-prefix observation for each mirrored digit pair."""
    with _completed_output_buffer(width, digits, ledger=ledger, scratch=scratch):
        return mirror_palindrome(width, scratch.__getitem__)


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
