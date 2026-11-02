"""Exact source-owned phase and bounded cyclotomic rank paths."""

from __future__ import annotations

from math import isqrt
from typing import Never

import pytest

from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.ordered_rank import (
    ORDERED_BOUNDARY_NODE_COST,
    OrderedRankBoundary2310,
)
from number_compiler.sequences.prime.select import PrimePrefixRank


@pytest.mark.parametrize("stage", ("boundary", "suffix"))
def test_optional_rank_failure_releases_scratch_and_keeps_inventory_exact(
    stage: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    def fail(*args: object, **kwargs: object) -> Never:
        raise ArithmeticError("rank construction interrupted")

    if stage == "boundary":
        monkeypatch.setattr(OrderedRankBoundary2310, "build", fail)
    else:
        monkeypatch.setattr(
            "number_compiler.sequences.prime.coprime_rank.ordered_cyclotomic_suffix_rank",
            fail,
        )
    owner = CoprimeRankDAG((2, 3, 5, 7, 11, 13, 17, 19))
    try:
        owner.validate_consecutive_prefix()
        with pytest.raises(ArithmeticError, match="interrupted"):
            owner.count(100_000, 8)
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def _primes_through(limit: int) -> tuple[int, ...]:
    flags = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        flags[0] = 0
    if limit >= 1:
        flags[1] = 0
    for candidate in range(2, isqrt(limit) + 1):
        if flags[candidate]:
            flags[candidate * candidate : limit + 1 : candidate] = b"\x00" * (
                (limit - candidate * candidate) // candidate + 1
            )
    return tuple(value for value in range(2, limit + 1) if flags[value])


def _prefix_rank(limit: int, factors: tuple[int, ...]) -> int:
    return sum(
        1 for value in range(1, limit + 1) if all(value % factor for factor in factors)
    )


def _boundary_nodes(owner: CoprimeRankDAG) -> int:
    inventory = owner.ledger.inventory()
    return next(
        item.nodes for item in inventory if item.name == "prime.rank.ordered_boundary"
    )


def test_phase_lane_scans_ordered_odd_prefix_and_enforces_stage_budget() -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7))
    try:
        owner.validate_consecutive_prefix()
        prime, tested, complete = owner.advance_verified_phase_lane(10, max_stages=20)
        assert prime is None
        assert tested == 1
        assert complete

        with pytest.raises(ValueError, match="stage budget"):
            owner.advance_verified_phase_lane(11, max_stages=4)
        prime, tested, complete = owner.advance_verified_phase_lane(11, max_stages=20)
        assert (prime, tested, complete) == (11, 2, False)
        assert owner.primes == (2, 3, 5, 7, 11)
    finally:
        owner.close()


def test_prime_prefix_cover_matches_independent_sieve_through_million() -> None:
    owner = PrimePrefixRank(
        max_states=200_000,
        max_work=10_000_000,
        max_stages=2_000,
    )
    try:
        owner.cover(1_000_000)
        expected = _primes_through(isqrt(1_000_000))
        assert owner.dag.primes == expected
        assert owner.covered_root == 1_000
        assert owner.discovery_queries > 0
    finally:
        owner.close()


def test_ordered_mobius_and_2310_suffix_rank_match_independent_count() -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7, 11, 13, 17, 19, 23))
    mask_owner = CoprimeRankDAG((2, 3, 5, 7, 11, 13, 17, 19, 23))
    deep_owner = CoprimeRankDAG((2, 3, 5, 7, 11, 13, 17, 19, 23, 29))
    try:
        owner.validate_consecutive_prefix()
        for depth in range(1, 10):
            factors = owner.primes[:depth]
            for limit in (1, 2, 7, 10, 29, 210, 2_309, 2_310, 2_311, 25_311):
                assert owner.count(limit, depth) == _prefix_rank(limit, factors)
        for depth in range(5, 10):
            factors = owner.primes[:depth]
            running = 0
            for limit in range(1, 2_400):
                running += int(all(limit % factor for factor in factors))
                assert owner.count(limit, depth) == running
        assert owner.count(100_000, 8) == _prefix_rank(100_000, owner.primes[:8])
        assert owner.count(100_000, 9) == _prefix_rank(100_000, owner.primes[:9])
        assert _boundary_nodes(owner) == ORDERED_BOUNDARY_NODE_COST
        mask_owner.validate_consecutive_prefix()
        assert mask_owner.count(100_000, 8) == _prefix_rank(
            100_000, mask_owner.primes[:8]
        )
        for limit in range(1, 2_311):
            assert mask_owner.count(limit, 8) == _prefix_rank(
                limit, mask_owner.primes[:8]
            )
        assert _boundary_nodes(mask_owner) == ORDERED_BOUNDARY_NODE_COST

        deep_owner.validate_consecutive_prefix()
        assert deep_owner.count(100_000, 10) == _prefix_rank(
            100_000, deep_owner.primes[:10]
        )
    finally:
        owner.close()
        mask_owner.close()
        deep_owner.close()
    assert owner.ledger.entries == 0
    assert mask_owner.ledger.entries == 0
    assert deep_owner.ledger.entries == 0


def test_unverified_factor_descriptor_does_not_admit_ordered_boundary() -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7, 11))
    try:
        expected = _prefix_rank(10_000, (2, 3, 5, 7, 11))
        assert owner.count(10_000, 5) == expected
        assert _boundary_nodes(owner) == 0
    finally:
        owner.close()


def test_low_work_query_skips_optional_2310_boundary() -> None:
    owner = CoprimeRankDAG(
        (2, 3, 5, 7, 11),
        max_work=1_000,
    )
    try:
        owner.validate_consecutive_prefix()
        assert owner.count(100_000, 5) == _prefix_rank(100_000, (2, 3, 5, 7, 11))
        assert _boundary_nodes(owner) == 0
    finally:
        owner.close()
