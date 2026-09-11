"""Exact hyperbolic floor-quotient carrier for prime-count summaries.

The distinct values ``floor(n/i)`` number only ``O(sqrt(n))``.  A combinatorial
sieve over those canonical quotient classes computes ``pi(n)`` without storing
an input prime sequence or materializing the prime bitmap.  This is an exact
nonlinear projection carrier for count/first-prime experiments; its state still
grows as ``sqrt(n)``, so it is not the desired polylogarithmic prime power.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import isqrt

from number_compiler.sequences.prime.set import PrimeBlockSummary


@dataclass(frozen=True, slots=True)
class PrimeCountQuotientResult:
    n: int
    count: int
    quotient_states: int
    sieve_updates: int
    discovered_primes: int


def prime_count_quotient(n: int) -> PrimeCountQuotientResult:
    n = int(n)
    if n < 2:
        return PrimeCountQuotientResult(n, 0, max(0, n + 1), 0, 0)
    root = isqrt(n)
    values = sorted(
        set(range(1, root + 1)) | {n // i for i in range(1, root + 1)},
        reverse=True,
    )
    count = {v: v - 1 for v in values}
    updates = 0
    discovered = 0
    for p in range(2, root + 1):
        if count[p] <= count[p - 1]:
            continue
        discovered += 1
        before_p = count[p - 1]
        p2 = p * p
        for v in values:
            if v < p2:
                break
            count[v] -= count[v // p] - before_p
            updates += 1
    return PrimeCountQuotientResult(n, count[n], len(values), updates, discovered)


@dataclass(frozen=True, slots=True)
class PrimeBlockQuotientResult:
    start: int
    length: int
    summary: PrimeBlockSummary
    pi_queries: int
    max_quotient_states: int
    total_sieve_updates: int


def prime_block_summary_quotient(start: int, length: int) -> PrimeBlockQuotientResult:
    """Return prime count + first prime for odd candidates ``start+2*j``."""
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length < 0:
        raise ValueError((start, length))
    if length == 0:
        return PrimeBlockQuotientResult(start, 0, PrimeBlockSummary.empty(), 0, 0, 0)
    high = start + 2 * (length - 1)
    cache: dict[int, PrimeCountQuotientResult] = {}

    def query(n: int) -> PrimeCountQuotientResult:
        old = cache.get(n)
        if old is not None:
            return old
        result = prime_count_quotient(n)
        cache[n] = result
        return result

    base = query(start - 1).count
    high_count = query(high).count
    block_count = high_count - base
    first_index = None
    if block_count:
        lo, hi = 0, length - 1
        while lo < hi:
            mid = (lo + hi) // 2
            if query(start + 2 * mid).count > base:
                hi = mid
            else:
                lo = mid + 1
        first_index = lo
    summary = PrimeBlockSummary(length, block_count, first_index)
    return PrimeBlockQuotientResult(
        start,
        length,
        summary,
        len(cache),
        max((r.quotient_states for r in cache.values()), default=0),
        sum(r.sieve_updates for r in cache.values()),
    )


__all__ = [
    "PrimeCountQuotientResult",
    "prime_count_quotient",
    "PrimeBlockQuotientResult",
    "prime_block_summary_quotient",
]
