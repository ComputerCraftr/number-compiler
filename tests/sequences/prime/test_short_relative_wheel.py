"""Source-authenticated short relative prime selection."""

from __future__ import annotations

from math import isqrt
from typing import TYPE_CHECKING

import pytest

from number_compiler.resources.metric_keys.prime import (
    PRIME_SUCCESSOR_SHORT_WHEEL_BATCHES,
    PRIME_SUCCESSOR_SHORT_WHEEL_PROBES,
)
from number_compiler.resources.process_cache import (
    ProcessCache,
    temporary_process_cache,
)
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.select import (
    PrimePrefixRank,
    nth_prime_at_or_after,
)
from tests.support.prime_actions import primes_through

if TYPE_CHECKING:
    from number_compiler.sequences.prime.factor_source import PrimeFactorSourceIdentity


def test_short_scan_executes_before_rank_or_xor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("short scan built an unrequested rank or XOR frontier")

    monkeypatch.setattr(PrimePrefixRank, "count_prime_interval", forbidden)
    monkeypatch.setattr(CoprimeRankDAG, "first_survivor_xor_bellman", forbidden)
    for start, index, expected in (
        (10_000_000, 0, 10_000_019),
        (1_000_000, 20, 1_000_253),
        (100_000, 10, 100_153),
    ):
        result, metrics = nth_prime_at_or_after(start, index)
        assert result == expected
        assert metrics.block_compilations == metrics.descent_rounds == 0
        counters = dict(metrics.scheduler_counters)
        assert counters[PRIME_SUCCESSOR_SHORT_WHEEL_PROBES] > 0
        assert counters[PRIME_SUCCESSOR_SHORT_WHEEL_BATCHES] > 0
        assert metrics.dag_states > 0
        assert metrics.parent_gap_positions_materialized == 0


@pytest.mark.parametrize("start", (10_000, 10_001, 10_007, 16_000, 100_000, 100_001))
def test_short_scan_matches_independent_sieve(start: int) -> None:
    oracle = tuple(p for p in primes_through(120_000) if p >= start)
    for index in (0, 1, 3, 20, 64, 128):
        result, metrics = nth_prime_at_or_after(start, index)
        assert result == oracle[index]
        assert metrics.block_compilations == 0


def test_short_scan_work_and_stage_limits() -> None:
    result, metrics = nth_prime_at_or_after(10_000_000, 0)
    assert result == 10_000_019
    assert metrics.projection_work < 20_000
    assert dict(metrics.scheduler_counters)[PRIME_SUCCESSOR_SHORT_WHEEL_PROBES] == 6
    with pytest.raises(ValueError, match="work budget"):
        nth_prime_at_or_after(10_000_000, 0, max_work=3000)
    with pytest.raises(ValueError, match="stage budget"):
        nth_prime_at_or_after(10_000_000, 0, max_stages=50)


def test_short_scan_rejects_changed_factor_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def wrong_source(
        _self: CoprimeRankDAG, _identity: PrimeFactorSourceIdentity
    ) -> bool:
        return False

    monkeypatch.setattr(CoprimeRankDAG, "is_current_factor_source", wrong_source)
    with pytest.raises(RuntimeError, match="prime prefix coverage is incomplete"):
        nth_prime_at_or_after(1_000_000, 0)


def test_short_scan_shared_prefix_keeps_authority() -> None:
    with temporary_process_cache(ProcessCache()):
        first, cold = nth_prime_at_or_after(100_000, 10, shared_cache=True)
        second, warm = nth_prime_at_or_after(100_000, 10, shared_cache=True)
        assert first == second == 100_153
        assert cold.discovery_queries > 0
        assert warm.discovery_queries == 0
        assert warm.shared_cache_hits > 0


@pytest.mark.parametrize(("start", "index"), ((1000, 3), (100_000, 130)))
def test_outside_short_scan_retains_rank_descent(start: int, index: int) -> None:
    result, metrics = nth_prime_at_or_after(start, index)
    expected = tuple(p for p in primes_through(start + 5000) if p >= start)[index]
    assert result == expected
    assert metrics.block_compilations > 0


def test_short_scan_square_boundary() -> None:
    for start in (10_200, 10_201, 10_202, 10_403, 10_404, 10_405):
        got, _ = nth_prime_at_or_after(start, 0)
        assert got in primes_through(got)
        assert all(got % p for p in primes_through(isqrt(got)))
        assert all(
            candidate not in primes_through(got) for candidate in range(start, got)
        )
