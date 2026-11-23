"""Source-authenticated weighted interval and wheel regressions."""

from __future__ import annotations

from math import gcd
from random import Random

import pytest

from number_compiler.resources.metric_keys import prime as prime_metrics
from number_compiler.resources.owned_memo import LedgerReservation
from number_compiler.resources.process_cache import clear_process_cache
from number_compiler.sequences.prime import weighted_cutoff
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.ordered_rank import (
    wheel_210_count,
    wheel_210_value,
)
from number_compiler.sequences.prime.select import PrimePrefixRank
from number_compiler.sequences.prime.weighted_cutoff import (
    LazyBasisPrefixMasks,
    SignedCutoffRow,
    WeightedCutoffMetrics,
)

_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)


def test_wheel_ordinal_round_trip() -> None:
    for ordinal in range(1, 3000):
        value = wheel_210_value(ordinal)
        assert gcd(value, 210) == 1
        assert wheel_210_count(value) == ordinal
        assert wheel_210_count(value - 1) == ordinal - 1


def test_row_promotes_cancels_and_reactivates() -> None:
    row = SignedCutoffRow()
    assert row.add(9, 3) == (0, 0, 0)
    assert row.add(7, -4) == (1, 0, 0)
    assert row.add(9, -3) == (0, 1, 1)
    assert row.add(7, 4) == (0, 0, 1)
    assert not row
    assert row.add(11, 2) == (0, 0, 0)
    assert row.take() == ((11, 2),)


@pytest.mark.parametrize("fused", (False, True))
def test_weighted_intervals_match_exact_independent_counts(fused: bool) -> None:
    owner = CoprimeRankDAG(_PRIMES, max_work=5_000_000)
    try:
        owner.validate_consecutive_prefix()
        initial_entries = owner.ledger.entries
        rng = Random(20261121)
        for _ in range(500):
            low = rng.randrange(0, 4000)
            high = low + rng.randrange(0, 250)
            depth = rng.randrange(4, len(_PRIMES) + 1)
            expected = sum(
                all(value % factor for factor in _PRIMES[:depth])
                for value in range(low + 1, high + 1)
            )
            assert (
                owner.count_weighted_interval(low, high, depth, fused_masks=fused)
                == expected
            )
            assert owner.ledger.entries == initial_entries
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_weighted_refuses_unverified_factor_prefix_and_releases_scratch() -> None:
    owner = CoprimeRankDAG((2, 3, 5, 11))
    try:
        with pytest.raises(ValueError):
            owner.count_weighted_interval(0, 1000, 4)
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


@pytest.mark.parametrize("fused", (False, True))
@pytest.mark.parametrize(
    "low,high",
    ((0, 0), (0, 1), (1, 2), (10, 21), (11, 19), (11, 22), (12, 23), (13, 24)),
)
def test_weighted_interval_one_and_single_multiple_boundaries(
    low: int, high: int, fused: bool
) -> None:
    owner = CoprimeRankDAG(_PRIMES)
    try:
        expected = sum(
            all(value % factor for factor in _PRIMES[:5])
            for value in range(low + 1, high + 1)
        )
        assert (
            owner.count_weighted_interval(low, high, 5, fused_masks=fused) == expected
        )
    finally:
        owner.close()


def test_weighted_refusal_releases_query_scratch() -> None:
    owner = CoprimeRankDAG(_PRIMES)
    try:
        owner.validate_consecutive_prefix()
        before = owner.ledger.entries, owner.ledger.nodes
        owner.max_work = owner.work + 1
        with pytest.raises(ValueError, match="work budget"):
            owner.count_weighted_interval(0, 4000, len(_PRIMES))
        assert (owner.ledger.entries, owner.ledger.nodes) == before
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_weighted_state_refusal_releases_query_scratch() -> None:
    owner = CoprimeRankDAG(_PRIMES)
    try:
        owner.validate_consecutive_prefix()
        before = owner.ledger.entries, owner.ledger.nodes
        owner.max_states = owner.ledger.entries - owner.factor_count + 1
        with pytest.raises(ValueError, match="state budget"):
            owner.count_weighted_interval(0, 4000, len(_PRIMES))
        assert (owner.ledger.entries, owner.ledger.nodes) == before
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_prefix_masks_nonmonotone_cutoffs() -> None:
    owner = CoprimeRankDAG(_PRIMES)
    scratch = owner.ledger.register("test.prime.mask", "mask scratch")
    try:
        owner.validate_consecutive_prefix()
        with LedgerReservation(owner.ledger, scratch) as reserve:
            masks = LazyBasisPrefixMasks(
                owner,
                owner.primes,
                WeightedCutoffMetrics(),
                lambda entries, nodes: reserve.reserve(entries=entries, nodes=nodes),
            )
            high = masks.ordinal_limit
            for depth in (15, 5, 11, 4, 14, 7):
                expected = sum(
                    all(wheel_210_value(i) % p for p in _PRIMES[:depth])
                    for i in range(1, high + 1)
                )
                assert masks.count(0, high, depth) == expected
    finally:
        owner.ledger.mark_disposed(scratch)
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_mask_capacity_falls_back_to_exact_weighted_recursion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner = CoprimeRankDAG(_PRIMES)
    try:
        owner.validate_consecutive_prefix()
        expected = owner.count_weighted_interval(0, 10000, len(_PRIMES))
        monkeypatch.setattr(weighted_cutoff, "_MASK_ORDINAL_CAP", 1)
        assert (
            owner.count_weighted_interval(0, 10000, len(_PRIMES), fused_masks=True)
            == expected
        )
    finally:
        owner.close()


@pytest.mark.parametrize("fused", (False, True))
@pytest.mark.parametrize(
    "start,index,expected", ((0, 1000, 7927), (150000, 200, 152293))
)
def test_weighted_selector_consumes_authenticated_prefix(
    start: int, index: int, expected: int, fused: bool
) -> None:
    owner = PrimePrefixRank(
        max_states=1_000_000,
        max_work=5_000_000,
        max_stages=10_000,
        _weighted=True,
        _fused_masks=fused,
    )
    try:
        assert owner.count_prime_interval(max(2, start), expected) == index
        assert owner.count_prime_interval(expected, expected + 1) == 1
    finally:
        owner.close()


def test_issued_interval_hit_avoids_refold_and_reset_rejects_stale(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()

    def new_owner() -> PrimePrefixRank:
        return PrimePrefixRank(
            max_states=131_072,
            max_work=1_000_000,
            max_stages=4096,
            shared_cache=True,
            _weighted=True,
        )

    try:
        first = new_owner()
        try:
            expected = first.count_prime_interval(150_000, 152_000)
            first.publish()
        finally:
            first.close()
        second = new_owner()
        try:

            def forbidden(*_args: object, **_kwargs: object) -> int:
                raise AssertionError("warm interval rebuilt its weighted children")

            monkeypatch.setattr(CoprimeRankDAG, "count_weighted_interval", forbidden)
            assert second.count_prime_interval(150_000, 152_000) == expected
            assert (
                second.dag.ledger.counters[prime_metrics.PRIME_WEIGHTED_INTERVAL_HITS]
                == 1
            )
            bounded = PrimePrefixRank(
                max_states=131_072,
                max_work=999_999,
                max_stages=4096,
                shared_cache=True,
                _weighted=True,
            )
            try:
                with pytest.raises(AssertionError, match="weighted children"):
                    bounded.count_prime_interval(150_000, 152_000)
            finally:
                bounded.close()
            clear_process_cache()
            with pytest.raises(RuntimeError, match="lease|generation|stale"):
                second.count_prime_interval(150_000, 152_000)
        finally:
            second.close()
        third = new_owner()
        try:
            with pytest.raises(AssertionError, match="weighted children"):
                third.count_prime_interval(150_000, 152_000)
        finally:
            third.close()
    finally:
        clear_process_cache()
