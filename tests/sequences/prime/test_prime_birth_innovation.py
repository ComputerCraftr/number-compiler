"""Independent finite rank and authority checks for prime-birth elimination."""

from __future__ import annotations

from math import gcd, isqrt, prod
from typing import Never

import pytest

from number_compiler.resources.metric_keys import prime as metric
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG


def _primes() -> tuple[int, ...]:
    return tuple(
        value
        for value in range(2, 98)
        if all(value % divisor for divisor in range(2, isqrt(value) + 1))
    )


@pytest.mark.parametrize("limit", (100, 120, 960, 961, 962, 3001))
def test_issued_suffix_matches_independent_gcd_rank(limit: int) -> None:
    factors = _primes()
    owner = CoprimeRankDAG(factors)
    try:
        owner.validate_consecutive_prefix()
        for depth in (5, 8, len(factors)):
            modulus = prod(factors[:depth])
            assert owner.count(limit, depth) == sum(
                gcd(value, modulus) == 1 for value in range(1, limit + 1)
            )
        assert owner.ledger.counters[metric.PRIME_BIRTH_INNOVATION_COLLAPSES] > 0
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_missing_prime_cannot_authorize_suffix_elimination() -> None:
    factors = (2, 3, 5, 7, 13, 17)
    owner = CoprimeRankDAG(factors)
    try:
        with pytest.raises(ValueError):
            owner.validate_consecutive_prefix()
        assert owner.count(200) == sum(
            gcd(value, prod(factors)) == 1 for value in range(1, 201)
        )
        assert metric.PRIME_BIRTH_INNOVATION_COLLAPSES not in owner.ledger.counters
    finally:
        owner.close()


def test_cached_rank_precedes_quotient_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner = CoprimeRankDAG(_primes())
    try:
        owner.validate_consecutive_prefix()
        expected = owner.count(3001)
        before = dict(owner.ledger.counters)

        def forbidden(_value: int) -> Never:
            raise AssertionError("cached parent rediscovered its square-root boundary")

        monkeypatch.setattr(
            "number_compiler.sequences.prime.coprime_rank.isqrt", forbidden
        )
        assert owner.count(3001) == expected
        assert dict(owner.ledger.counters) == before
    finally:
        owner.close()


def test_budget_refusal_precedes_sqrt_and_leaves_no_pending_frames(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner = CoprimeRankDAG(_primes())
    try:
        owner.validate_consecutive_prefix()
        owner.max_work = owner.work + 1
        before = dict(owner.ledger.counters)

        def forbidden(_value: int) -> Never:
            raise AssertionError("refused rank computed an uncharged square root")

        monkeypatch.setattr(
            "number_compiler.sequences.prime.coprime_rank.isqrt", forbidden
        )
        with pytest.raises(ValueError, match="work budget"):
            owner.count(3001)
        assert owner.pending_frames == 0
        assert dict(owner.ledger.counters) == before
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()
