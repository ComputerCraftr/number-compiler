"""Source-qualified progression cutoff and sparse symbolic shift regressions."""

from __future__ import annotations

from math import gcd, prod
from random import Random

import pytest

from number_compiler.resources.metric_keys import prime as metric
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.set import AdditiveTranslation
from tests.support.prime_actions import primes_through


def test_progression_suffix_matches_literal_shared_and_coprime_moduli() -> None:
    factors = primes_through(53)
    owner = CoprimeRankDAG(factors, max_work=2_000_000)
    try:
        owner.validate_consecutive_prefix()
        wheel = prod(factors)
        for modulus in (4, 8, 15, 24):
            for bound in (72, 118, 423, 1000):
                for residue in range(modulus):
                    expected = sum(
                        gcd(n, wheel) == 1 and n % modulus == residue
                        for n in range(1, bound + 1)
                    )
                    assert owner.count_progression(bound, modulus, residue) == expected
        assert owner.ledger.counters[metric.PRIME_BIRTH_INNOVATION_COLLAPSES] > 0
        assert owner.pending_frames == 0
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_unverified_prefix_never_uses_birth_cutoff() -> None:
    factors = (2, 3, 5, 7, 13, 17)
    owner = CoprimeRankDAG(factors)
    try:
        with pytest.raises(ValueError, match="consecutive"):
            owner.validate_consecutive_prefix()
        for residue in range(8):
            assert owner.count_progression(200, 8, residue) == sum(
                all(n % p for p in factors) and n % 8 == residue for n in range(1, 201)
            )
        assert metric.PRIME_BIRTH_INNOVATION_COLLAPSES not in owner.ledger.counters
    finally:
        owner.close()


def test_progression_budget_refusal_cleans_pending_frames() -> None:
    owner = CoprimeRankDAG(primes_through(100))
    try:
        owner.validate_consecutive_prefix()
        owner.max_work = owner.work + 1
        with pytest.raises(ValueError, match="work budget"):
            owner.count_progression(10_000, 16, 3)
        assert owner.pending_frames == 0
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()


def test_sparse_shifts_carry_without_visiting_empty_positions() -> None:
    huge = 10**100
    one = AdditiveTranslation.power_of_two(0)
    other = AdditiveTranslation.power_of_two(huge)
    assert one.then(other).pow2_exponents == (0, huge)
    assert one.then(other).then(other).pow2_exponents == (0, huge + 1)
    rng = Random(91827)
    for _ in range(100):
        a, b = rng.getrandbits(128), rng.getrandbits(128)
        aa, bb = map(AdditiveTranslation.from_int, (a, b))
        assert aa.then(bb).materialize() == a + b
