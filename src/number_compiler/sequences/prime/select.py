"""Exact rank/select over the canonical finite prime-block projector.

The selector never constructs a whole unbounded prime sequence.  It uses the
existing residual-divisor block compiler for counts, narrows to one bounded
leaf, and only then materializes a tiny leaf bitmap to select the requested
prime.  All projection work is exposed for regression accounting.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.sequences.prime.lane_quotient import (
    canonical_prime_base_period,
    compile_prime_block_lane_quotient,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


@dataclass(frozen=True, slots=True)
class PrimeRankSelectMetrics:
    block_compilations: int
    projection_work: int
    max_block_length: int
    leaf_length: int
    expansion_rounds: int
    descent_rounds: int


def _select_set_bit(mask: int, rank: int) -> int:
    rank = int(rank)
    if rank < 0:
        raise ValueError(rank)
    value = int(mask)
    for _ in range(rank):
        if not value:
            raise IndexError(rank)
        value &= value - 1
    if not value:
        raise IndexError(rank)
    bit = value & -value
    return bit.bit_length() - 1


def nth_prime_at_or_after(
    start: int, index: int, *, leaf_length: int = 128
) -> tuple[int, PrimeRankSelectMetrics]:
    """Return zero-based prime ``index`` at or above ``start``.

    The special prime 2 is handled before entering the odd-candidate compiler.
    Every larger candidate is represented as ``odd_start + 2*j``.
    """
    start, index, leaf_length = int(start), int(index), int(leaf_length)
    if start < 0 or index < 0 or leaf_length < 8:
        raise ValueError((start, index, leaf_length))

    remaining = index
    if start <= 2:
        if remaining == 0:
            return 2, PrimeRankSelectMetrics(0, 0, 0, 0, 0, 0)
        remaining -= 1
        odd_start = 3
    else:
        odd_start = start if start & 1 else start + 1
        odd_start = max(3, odd_start)

    # A modest overestimate keeps ordinary nth-prime queries to one expansion
    # while retaining exact doubling if a sparse/high-start interval needs more.
    length = max(leaf_length, 16 * (remaining + 1))
    compilations = work = expansions = descents = 0
    max_length = 0

    def compile_count(block_start: int, block_length: int) -> int:
        nonlocal compilations, work, max_length
        q = compile_prime_block_lane_quotient(
            block_start,
            block_length,
            base_period=canonical_prime_base_period(block_length),
            include_primary_jet=False,
            include_wheel_cyclotomic=False,
        )
        compilations += 1
        work += q.projection_work
        max_length = max(max_length, block_length)
        return q.summary.count

    while True:
        count = compile_count(odd_start, length)
        if count > remaining:
            break
        remaining -= count
        odd_start += 2 * length
        length *= 2
        expansions += 1

    block_start = odd_start
    block_length = length
    while block_length > leaf_length:
        left_length = block_length // 2
        left_count = compile_count(block_start, left_length)
        if remaining < left_count:
            block_length = left_length
        else:
            remaining -= left_count
            block_start += 2 * left_length
            block_length -= left_length
        descents += 1

    leaf = project_odd_prime_block(block_start, block_length)
    offset = _select_set_bit(leaf.prime_mask, remaining)
    value = block_start + 2 * offset
    return value, PrimeRankSelectMetrics(
        compilations,
        work,
        max_length,
        block_length,
        expansions,
        descents,
    )


__all__ = ["PrimeRankSelectMetrics", "nth_prime_at_or_after"]
