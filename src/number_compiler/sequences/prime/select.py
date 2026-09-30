"""Source-derived finite prime rank/select over the canonical wheel count DAG.

A query shares factor discovery and all ranks. No parent wheel gap cycle or
candidate bitmap is constructed. Factor-stage growth is explicit, bounded work;
this is not a claim of logarithmic source discovery for unbounded prime queries.
"""

from __future__ import annotations

from contextlib import ExitStack, closing
from dataclasses import dataclass
from math import isqrt
from os import urandom
from typing import cast

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
    CacheStats,
    get_process_cache,
)
from number_compiler.sequences.prime.coprime_rank import (
    MAX_SHARED_FACTOR_STAGES,
    CoprimeRankDAG,
)

_PRIME_CACHE_NAMESPACE = "prime.coprime-rank"
_PRIME_CACHE_VERSION = "positive-integers-least-survivor-v1"
_PRIME_CACHE_ISSUER = urandom(32)
_PRIME_CACHE_SOURCE = (
    "positive-integers",
    "consecutive-prime-prefix",
    _PRIME_CACHE_ISSUER,
)
_PREFIX_KEY = ("admitted-prefix",)


@dataclass(frozen=True, slots=True)
class PrimeRankSelectMetrics:
    block_compilations: int
    projection_work: int
    max_block_length: int
    leaf_length: int
    expansion_rounds: int
    descent_rounds: int
    dag_states: int = 0
    cache_hits: int = 0
    factor_stages: int = 0
    discovery_queries: int = 0
    peak_pending_frames: int = 0
    retained_entries: int = 0
    arithmetic_bit_work: int = 0
    parent_gap_positions_materialized: int = 0
    shared_cache_hits: int = 0
    shared_cache_misses: int = 0
    shared_cache_entries: int = 0
    shared_cache_bytes: int = 0
    request_allocations: int = 0
    shared_cache_evictions: int = 0
    shared_cache_bypasses: int = 0
    shared_cache_publications: int = 0
    admission_work: int = 0
    scheduler_work: int = 0
    scheduler_allocations: int = 0
    scheduler_counters: tuple[tuple[str, int], ...] = ()


def _validate_cached_prefix(payload: object) -> tuple[int, tuple[int, ...], int, int]:
    """Validate the issued manifest header; demanded factors are admitted lazily."""
    if type(payload) is not tuple or len(payload) != 3:
        raise RuntimeError("invalid shared prime prefix manifest")
    covered_root, raw_factors, state_count = payload
    if (
        type(covered_root) is not int
        or covered_root < 2
        or type(raw_factors) is not tuple
        or not raw_factors
        or len(raw_factors) > MAX_SHARED_FACTOR_STAGES
        or type(state_count) is not int
        or state_count < 0
    ):
        raise RuntimeError("invalid shared prime prefix manifest")
    factors = cast(tuple[int, ...], raw_factors)
    if (
        type(factors[0]) is not int
        or type(factors[-1]) is not int
        or factors[0] != 2
        or factors[-1] > covered_root
    ):
        raise RuntimeError("invalid shared prime prefix manifest")
    return covered_root, factors, state_count, 1


class PrimePrefixRank:
    """Admit a horizon by discovering its consecutive prime factor prefix.

    Start with the prime 2. If the current wheel has a survivor > 1 below the
    desired square root, its least such survivor is prime: a composite survivor
    has a smaller prime divisor which would also survive. Appending that value
    preserves consecutive-prefix completeness. Phi(root,k)=1 proves coverage.
    """

    def __init__(
        self,
        *,
        max_states: int,
        max_work: int,
        max_stages: int,
        shared_cache: bool = False,
    ) -> None:
        if type(max_stages) is not int or max_stages < 1:
            raise ValueError("prime stage budget must be a positive integer")
        self.max_stages = max_stages
        if type(shared_cache) is not bool:
            raise TypeError("prime shared-cache flag must be a boolean")
        self._lease: CacheLease | None = None
        self._cache_start: CacheStats | None = None
        self._imported_states = 0
        self._cached_factors: tuple[int, ...] = (2,)
        self._cached_covered_root = 2
        self._cached_validated_count = 1
        self.admission_work = 0
        factors: tuple[int, ...] = (2,)
        covered_root, validation_work = 2, 0
        if shared_cache:
            lease = get_process_cache().acquire(
                _PRIME_CACHE_NAMESPACE, _PRIME_CACHE_VERSION, _PRIME_CACHE_SOURCE
            )
            self._lease = lease
            self._cache_start = lease.stats()
            try:
                cached = lease.get(_PREFIX_KEY, MISSING)
                if cached is not MISSING:
                    covered_root, factors, self._imported_states, validation_work = (
                        _validate_cached_prefix(cached)
                    )
                    self._cached_factors = factors
                    self._cached_covered_root = covered_root
            except BaseException:
                lease.close()
                self._lease = None
                raise
        try:
            self.dag = CoprimeRankDAG(
                (2,),
                max_states=max_states,
                max_work=max_work,
                # If the prior query needed more states than this request
                # admits, execute locally.  This makes a large warm query fail
                # at the same boundary while allowing a genuinely smaller one.
                shared_lease=(
                    self._lease if self._imported_states <= max_states else None
                ),
            )
            self.dag.charge_many(validation_work)
            self.admission_work = validation_work
        except BaseException:
            if self._lease is not None:
                self._lease.close()
                self._lease = None
            raise
        self.covered_root = 2
        self._committed_covered_root = 2
        self._covered_factor_authority = self.dag._factor_store_authority
        self._covered_factor_count = self.dag.factor_count
        self._covered_last_factor = self.dag.last_factor
        self._coverage_publishable = True
        self.discovery_queries = 0
        self._partial_query: object | None = None

    def _admit_cached_factors(self, root: int) -> None:
        """Import only the prefix required by this request's square-root bound."""
        self._coverage_publishable = False
        if (
            root >= self._cached_covered_root
            and self.dag.max_states is not None
            and self._imported_states > self.dag.max_states
        ):
            # Reusing the complete covered horizon also admits its recorded
            # recurrence footprint. Smaller horizons instead import a strict
            # prefix and construct their demanded Phi states locally.
            raise ValueError("prime state budget exceeded (--max-prime-states)")
        root = min(root, self._cached_covered_root)
        required = self.dag.factor_count
        while required < len(self._cached_factors):
            factor = self._cached_factors[required]
            if required >= self._cached_validated_count:
                self.dag.charge()
                self.admission_work += 1
                previous = self._cached_factors[required - 1]
                if type(factor) is not int or factor <= previous:
                    raise RuntimeError("invalid shared prime prefix manifest")
                self._cached_validated_count = required + 1
            if factor > root:
                break
            required += 1
        if required > self.max_stages:
            raise ValueError("prime stage budget exceeded (--max-prime-stages)")
        for factor in self._cached_factors[self.dag.factor_count : required]:
            # The cache partition includes a process-private issuer capability;
            # public/foreign partitions cannot enter this source binding.
            self.dag._append_issued_consecutive_factor(factor)
            self.admission_work += 1
        self.covered_root = max(self.covered_root, root)
        self._committed_covered_root = self.covered_root
        self._covered_factor_count = self.dag.factor_count
        self._covered_last_factor = self.dag.last_factor
        self._coverage_publishable = True

    def cover(self, high: int) -> None:
        if (
            type(self.covered_root) is not int
            or self.covered_root != self._committed_covered_root
        ):
            raise RuntimeError("prime prefix coverage is incomplete")
        self.dag.charge(high.bit_length())
        root = isqrt(high)
        if root <= self.covered_root:
            return
        if self.covered_root < self._cached_covered_root:
            self._admit_cached_factors(root)
            if root <= self.covered_root:
                return
        # The admitted prefix manifest is the reusable result of source
        # discovery. Publishing every internal discovery rank adds cold latency
        # and retains states that a warm query never consumes.
        self._coverage_publishable = False
        with self.dag.suspend_shared_publication():
            while True:
                self.discovery_queries += 1
                if self.dag.count(root) == 1:
                    self.covered_root = root
                    self._committed_covered_root = root
                    self._covered_factor_count = self.dag.factor_count
                    self._covered_last_factor = self.dag.last_factor
                    self._coverage_publishable = True
                    return
                if self.dag.factor_count >= self.max_stages:
                    raise ValueError("prime stage budget exceeded (--max-prime-stages)")
                lo, hi = self.dag.last_factor + 1, root
                while lo < hi:
                    self.dag.charge(lo.bit_length() + hi.bit_length())
                    mid = (lo + hi) // 2
                    self.discovery_queries += 1
                    if self.dag.count(mid) > 1:
                        hi = mid
                    else:
                        lo = mid + 1
                self.dag.append_consecutive_factor(lo)

    def count_leq(self, value: int) -> int:
        if value < 2:
            return 0
        self.cover(value)
        if value <= self.dag.last_factor:
            self.dag.charge(value.bit_length())
            return self.dag.factor_rank(value)
        # All composites <= value have a covered prime factor. Survivors are
        # exactly 1 and primes outside the descriptor; restore the known prefix.
        # Apply the last source-discovered prime as the actual zero-phase
        # partial successor action.  This avoids constructing its full W-period
        # while retaining the exact multiplication-bijection recurrence.
        return self.dag.count_via_fresh_successor(value) + self.dag.factor_count - 1

    def count_prime_interval(self, lower: int, upper: int) -> int:
        """Count primes in ``[lower, upper)`` through the admitted fresh-q image."""
        if (
            type(lower) is not int
            or type(upper) is not int
            or lower < 2
            or lower > upper
        ):
            raise ValueError("invalid production prime interval")
        if lower == upper:
            return 0
        self.cover(upper - 1)
        from number_compiler.sequences.prime.partial_successor_image import (
            PrimePartialSuccessorQuery,
        )

        query = self._partial_query
        if query is None:
            query = PrimePartialSuccessorQuery(self.dag)
            self._partial_query = query
        if type(query) is not PrimePartialSuccessorQuery:
            raise RuntimeError("prime query contains another image owner")
        return query.count_primes(lower, upper, self.dag.factor_count)

    def close(self) -> None:
        # The process pin must be released even if a local owner rejects cleanup.
        # Register in reverse ownership order; ExitStack runs every callback.
        with ExitStack() as cleanup:
            if self._lease is not None:
                cleanup.callback(self._lease.close)
            cleanup.callback(self.dag.close)
            if self._partial_query is not None:
                from number_compiler.sequences.prime.partial_successor_image import (
                    PrimePartialSuccessorQuery,
                )

                query = self._partial_query
                if type(query) is not PrimePartialSuccessorQuery:
                    raise RuntimeError("prime query contains another image owner")
                query.close()
                self._partial_query = None
        self._lease = None

    def publish(self) -> None:
        """Publish only admitted source metadata; selected endpoints stay local."""
        if (
            not self._coverage_publishable
            or type(self.covered_root) is not int
            or self.covered_root != self._committed_covered_root
            or self.dag._factor_store_authority is not self._covered_factor_authority
            or self.dag.factor_count != self._covered_factor_count
            or self.dag.last_factor != self._covered_last_factor
        ):
            raise RuntimeError("prime prefix coverage is incomplete")
        if self._lease is None or self.dag.factor_count > MAX_SHARED_FACTOR_STAGES:
            return
        if self.covered_root < self._cached_covered_root:
            return
        # This is the admitted recurrence footprint, not merely the smaller
        # number of root states retained by the process cache.  A warm request
        # therefore cannot use reuse to evade its state budget.
        state_count = max(self._imported_states, len(self.dag.memo))
        factors = self.dag.primes
        self._lease.put(_PREFIX_KEY, (self.covered_root, factors, state_count))

    def shared_metrics(self) -> tuple[int, int, int, int, int, int, int]:
        if self._lease is None or self._cache_start is None:
            return 0, 0, 0, 0, 0, 0, 0
        current = self._lease.stats()
        return (
            current.hits - self._cache_start.hits,
            current.misses - self._cache_start.misses,
            # Snapshot while this request owns its lease: payloads, partition
            # pins, and lease authorities are all retained cache entries.
            current.entries + current.lease_partitions + current.active_leases,
            current.bytes,
            current.evictions - self._cache_start.evictions,
            current.bypasses - self._cache_start.bypasses,
            current.puts - self._cache_start.puts,
        )


def nth_prime_at_or_after(
    start: int,
    index: int,
    *,
    leaf_length: int = 8,
    max_states: int = 131_072,
    max_work: int = 1_000_000,
    max_stages: int = 4096,
    shared_cache: bool = False,
) -> tuple[int, PrimeRankSelectMetrics]:
    """Return zero-based prime index at/above start, with finite work budgets.

    ``leaf_length`` remains the initial window-size hint for Python compatibility;
    rank descent now reaches a singleton without materializing a leaf bitmap.
    """
    start = require_integer(start, "prime start", 0)
    index = require_integer(index, "prime index", 0)
    leaf_length = require_integer(leaf_length, "prime initial window", 8)
    if start < 0 or index < 0 or leaf_length < 8:
        raise ValueError((start, index, leaf_length))
    if any(type(v) is not int or v < 1 for v in (max_states, max_work, max_stages)):
        raise ValueError(
            "prime states, work and stage budgets must be positive integers"
        )
    if type(shared_cache) is not bool:
        raise TypeError("prime shared-cache flag must be a boolean")
    remaining = index
    if start <= 2:
        if remaining == 0:
            return 2, PrimeRankSelectMetrics(0, 0, 0, 0, 0, 0)
        remaining -= 1
        odd_start = 3
    else:
        odd_start = start if start & 1 else start + 1
    # This is only a starting window, never an assumed prime-density bound.
    # Exact doubling handles sparse windows; smaller admission avoids discovering
    # unnecessary factor stages for the former 16*n odd-candidate overestimate.
    length = max(leaf_length, 4 * (remaining + 1))
    compilations = expansions = descents = max_length = 0
    context = PrimePrefixRank(
        max_states=max_states,
        max_work=max_work,
        max_stages=max_stages,
        shared_cache=shared_cache,
    )

    def compile_count(block_start: int, block_length: int) -> int:
        nonlocal compilations, max_length
        compilations += 1
        max_length = max(max_length, block_length)
        high = block_start + 2 * (block_length - 1)
        return context.count_prime_interval(block_start, high + 1)

    with closing(context):
        while True:
            count = compile_count(odd_start, length)
            if count > remaining:
                break
            remaining -= count
            odd_start += 2 * length
            length *= 2
            expansions += 1
        while length > 1:
            left_length = length // 2
            left_count = compile_count(odd_start, left_length)
            if remaining < left_count:
                length = left_length
            else:
                remaining -= left_count
                odd_start += 2 * left_length
                length -= left_length
            descents += 1
        dag = context.dag
        from number_compiler.sequences.prime.partial_successor_image import (
            PrimePartialSuccessorQuery,
        )

        partial = context._partial_query
        if type(partial) is not PrimePartialSuccessorQuery:
            raise RuntimeError("prime selection did not publish its partial successor")
        scheduler_work = dag.ledger.counters.get("prime_successor_scheduler_work", 0)
        scheduler_allocations = partial.peak_scheduler_entries
        context.publish()
        (
            shared_hits,
            shared_misses,
            shared_entries,
            shared_bytes,
            shared_evictions,
            shared_bypasses,
            shared_publications,
        ) = context.shared_metrics()
        return odd_start, PrimeRankSelectMetrics(
            compilations,
            dag.work,
            max_length,
            1,
            expansions,
            descents,
            len(dag.memo),
            dag.cache_hits,
            dag.factor_count,
            context.discovery_queries,
            dag.peak_pending_frames,
            len(dag.memo) + len(dag.progression_memo) + dag.factor_count,
            dag.arithmetic_bit_work,
            0,
            shared_hits,
            shared_misses,
            shared_entries,
            shared_bytes,
            len(dag.memo) + len(dag.progression_memo) + dag.factor_count,
            shared_evictions,
            shared_bypasses,
            shared_publications,
            context.admission_work,
            scheduler_work,
            scheduler_allocations,
            tuple(
                sorted(
                    (name, count)
                    for name, count in dag.ledger.counters.items()
                    if name.startswith(
                        (
                            "source_image_",
                            "prime_partial_successor_",
                            "prime_successor_",
                        )
                    )
                )
            ),
        )


__all__ = ["PrimeRankSelectMetrics", "nth_prime_at_or_after"]
