"""Demanded prime and deck observations of an admitted Collatz branch.

The prime labels are full-phase *possibility* classes.  They cannot select the
source's next valuation, prove safety, or stand in for the exact source cylinder.
This research consumer shares the ledger-owned partition implementation with
the Mahler observer; it does not maintain another refinement algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.branch_quotients import (
    PRIME_BANK,
    PrimeBucketWorkspace,
)
from number_compiler.sequences.collatz.saturated_future import (
    SaturatedCollatzOccurrence,
)


def _bank_prefix(primes: int | None) -> tuple[int, ...]:
    if primes is None:
        return PRIME_BANK
    if type(primes) is not int or not 0 <= primes <= len(PRIME_BANK):
        raise ValueError("prime prefix length lies outside the observer bank")
    return PRIME_BANK[:primes]


def collatz_prime_bucket_counts(
    workspace: PrimeBucketWorkspace, *, primes: int | None = None
) -> tuple[tuple[int, int], ...]:
    """Return class counts, charging and memoizing every demanded partition."""

    return tuple(
        (prime, len(set(workspace.partition("collatz", prime))))
        for prime in _bank_prefix(primes)
    )


def source_prime_bucket_vector(
    source: int, workspace: PrimeBucketWorkspace, *, primes: int | None = None
) -> tuple[int, ...]:
    """Observe ``u=-3*x-1`` without admitting a future source event."""

    if type(source) is not int or source <= 0 or not (source & 1):
        raise ValueError("Collatz prime observation requires a positive odd source")
    bank = _bank_prefix(primes)
    coordinate = -3 * source - 1
    return tuple(
        workspace.partition("collatz", prime)[coordinate % prime] for prime in bank
    )


@dataclass(frozen=True, slots=True)
class CoarseFutureContext:
    """A source-bound observation, never an action or successor identity."""

    deck: int
    prime_buckets: tuple[int, ...]
    descent_fiber_start: int | None


def observe_occurrence_context(
    occurrence: SaturatedCollatzOccurrence,
    source: int,
    workspace: PrimeBucketWorkspace,
    *,
    primes: int | None = None,
) -> CoarseFutureContext:
    """Project a source already admitted by this exact occurrence cylinder."""

    if type(occurrence) is not SaturatedCollatzOccurrence:
        raise TypeError("coarse Collatz context requires a saturated occurrence")
    # Admission precedes all partition work.  Equal prime or deck observations
    # do not allow a foreign source to borrow this occurrence's safety verdict.
    high_fiber = occurrence.source_high_fiber(source)
    return CoarseFutureContext(
        high_fiber & 63,
        source_prime_bucket_vector(source, workspace, primes=primes),
        occurrence.descent_fiber_start(),
    )


__all__ = [
    "CoarseFutureContext",
    "collatz_prime_bucket_counts",
    "observe_occurrence_context",
    "source_prime_bucket_vector",
]
