"""Non-semantic compiler summaries for exact pair-field formulas.

The summary is deliberately *not* stored in FormulaRoot.  It is arena/compiler
metadata keyed by the exact plane roots.  Powered code may consume a cached
summary, but may not synthesize one by scanning/evaluating positions while the
jump guard is active.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Literal, overload

from number_compiler.arithmetic.automata.guard import (
    JumpGuardViolation,
    in_powered_jump,
    record_summary_query,
)
from number_compiler.arithmetic.carry.carry_labels import (
    IDENTITY as I,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ONE as R1,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ZERO as R0,
)
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
)
from number_compiler.arithmetic.formula.types import RadixSpec


@dataclass(frozen=True, slots=True)
class BlockSummary:
    length: int
    all_threshold: bool
    first_reset: int | None
    last_reset: int | None
    first_reset_sign: int  # -1 below threshold, 0 no reset, +1 above
    last_reset_sign: int
    transfer: int  # I/R0/R1 for the whole block

    def __post_init__(self) -> None:
        if self.length <= 0:
            raise ValueError(self.length)
        if self.all_threshold:
            if any(x is not None for x in (self.first_reset, self.last_reset)):
                raise ValueError("all-threshold summary cannot contain reset positions")
            if self.first_reset_sign or self.last_reset_sign or self.transfer != I:
                raise ValueError("invalid all-threshold summary")
        else:
            if self.first_reset is None or self.last_reset is None:
                raise ValueError("non-threshold summary requires reset positions")
            if self.first_reset_sign not in (-1, 1) or self.last_reset_sign not in (
                -1,
                1,
            ):
                raise ValueError("invalid reset sign")
            expected = R1 if self.last_reset_sign > 0 else R0
            if self.transfer != expected:
                raise ValueError("transfer must match last effective reset")

    @property
    def growth_from_outer_symmetry(self) -> int:
        """Terminal carry for a symmetric pair field starting with carry zero.

        A palindrome's rightmost effective reset mirrors its first effective
        reset.  All-threshold words propagate the initial zero and do not grow.
        """
        return int((not self.all_threshold) and self.first_reset_sign > 0)


def summary_from_values(values: Sequence[int], spec: RadixSpec) -> BlockSummary:
    vals = tuple(map(int, values))
    if not vals:
        raise ValueError("empty values")
    t = spec.threshold
    reset = [i for i, value in enumerate(vals) if value != t]
    if not reset:
        return BlockSummary(len(vals), True, None, None, 0, 0, I)
    first, last = reset[0], reset[-1]
    fs = 1 if vals[first] > t else -1
    ls = 1 if vals[last] > t else -1
    return BlockSummary(len(vals), False, first, last, fs, ls, R1 if ls > 0 else R0)


def _key(arena: FormulaArena, root: FormulaRoot, spec: RadixSpec) -> tuple[object, ...]:
    return ("block-summary", spec.base, canonical_root_key(root, arena))


def register_summary(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec, summary: BlockSummary
) -> BlockSummary:
    if summary.length != root.width:
        raise ValueError((summary.length, root.width))
    arena.metadata_set(_key(arena, root, spec), summary)
    return summary


@overload
def get_summary(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec, *, required: Literal[True]
) -> BlockSummary: ...


@overload
def get_summary(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec, *, required: bool = False
) -> BlockSummary | None: ...


def get_summary(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec, *, required: bool = False
) -> BlockSummary | None:
    value = arena.metadata_get(_key(arena, root, spec))
    hit = isinstance(value, BlockSummary)
    record_summary_query(hit)
    if isinstance(value, BlockSummary):
        return value
    if required:
        if in_powered_jump():
            raise JumpGuardViolation(
                "powered jump requested a missing BlockSummary; summaries must be "
                "propagated by the compiler, never synthesized by positional scanning"
            )
        raise KeyError("BlockSummary not registered")
    return None


def compose_summaries(left: BlockSummary, right: BlockSummary) -> BlockSummary:
    """Exact concatenation summary.  Constant-size monoid metadata composition."""
    length = left.length + right.length
    if left.all_threshold and right.all_threshold:
        return BlockSummary(length, True, None, None, 0, 0, I)
    first: int | None
    last: int | None
    if not left.all_threshold:
        first = left.first_reset
        first_sign = left.first_reset_sign
    else:
        if right.first_reset is None:
            raise AssertionError("missing first reset")
        first = left.length + right.first_reset
        first_sign = right.first_reset_sign
    if not right.all_threshold:
        if right.last_reset is None:
            raise AssertionError("missing last reset")
        last = left.length + right.last_reset
        last_sign = right.last_reset_sign
    else:
        last = left.last_reset
        last_sign = left.last_reset_sign
    transfer = R1 if last_sign > 0 else R0
    return BlockSummary(length, False, first, last, first_sign, last_sign, transfer)


__all__ = [
    "R0",
    "R1",
    "BlockSummary",
    "I",
    "compose_summaries",
    "get_summary",
    "register_summary",
    "summary_from_values",
    "synthesize_symmetric_summary",
]


def synthesize_symmetric_summary(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec
) -> BlockSummary:
    """Build a summary by selectively probing only the outer threshold run.

    This helper is deliberately forbidden during a powered jump because it
    performs positional evaluation.  It is used by the ordinary/reference
    successor to populate compiler metadata for the newly constructed closed
    formula.  Symmetry makes the last reset the mirror of the first reset, so no
    whole-width carry scan is required.
    """
    from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

    forbid_in_powered_jump("synthesize_symmetric_summary")
    cached = get_summary(arena, root, spec)
    if cached is not None:
        return cached
    threshold = spec.threshold
    half = (root.width + 1) // 2
    for i in range(half):
        value = sum(
            arena.eval_closed_bit(plane, i) << bit
            for bit, plane in enumerate(root.planes)
        )
        if value != threshold:
            sign = 1 if value > threshold else -1
            j = root.width - 1 - i
            summary = BlockSummary(
                root.width, False, i, j, sign, sign, R1 if sign > 0 else R0
            )
            arena.metadata_increment("summary_selective_positions", i + 1)
            return register_summary(arena, root, spec, summary)
    arena.metadata_increment("summary_selective_positions", half)
    return register_summary(
        arena, root, spec, BlockSummary(root.width, True, None, None, 0, 0, I)
    )
