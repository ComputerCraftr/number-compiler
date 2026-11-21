"""Execution checks for the shared-factor 2-adic prime Bellman selector."""

from __future__ import annotations

from math import gcd

import pytest

from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from tests.support.prime_actions import prime_inverse_workspace, primes_through


def _oracle(x: int, factors: tuple[int, ...], modulus: int, residue: int) -> int:
    return sum(
        gcd(i, _product(factors)) == 1 and i % modulus == residue
        for i in range(1, x + 1)
    )


def _product(xs: tuple[int, ...]) -> int:
    result = 1
    for v in xs:
        result *= v
    return result


def test_shared_factor_progression_exact_without_bad_inverses() -> None:
    factors = (2, 3, 5, 7, 11, 13)
    owner = CoprimeRankDAG(factors)
    try:
        owner.validate_consecutive_prefix()
        for m in (2, 4, 8, 16, 32, 6, 10, 12, 24, 60, 15, 30):
            for x in (0, 1, 11, 29, 98, 210, 511):
                for r in range(m):
                    got = owner.count_progression(x, m, r)
                    assert got == _oracle(x, factors, m, r), (m, x, r)
        for r in (0, 1, 2, 3):
            assert owner.count_progression_interval(38, 94, 4, r) == sum(
                gcd(x, 30030) == 1 and x % 4 == r for x in range(38, 94)
            )
        assert not prime_inverse_workspace(owner)
        assert owner.pending_frames == 0
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0


def test_rank_and_leaf_bellman_agree_on_actual_prime_births() -> None:
    seq = primes_through(400)
    for depth in (4, 5, 7, 10, 13, 22, 40, 70):
        owner = CoprimeRankDAG(tuple(seq[:depth]), max_work=1_000_000)
        try:
            owner.validate_consecutive_prefix()
            last = seq[depth - 1]
            lower, upper = last + 1, 2 * last + 1
            rank = owner.first_survivor_xor_bellman(lower, upper, mode="rank")
            leaf = owner.first_survivor_xor_bellman(lower, upper, mode="leaf")
            assert rank is not None and leaf is not None
            assert rank.candidate == leaf.candidate == seq[depth]
            assert rank.first_changed_bit == leaf.first_changed_bit
            primorial = _product(tuple(seq[:depth]))
            p = seq[depth]
            full_xor = primorial ^ (primorial * p)
            j = (full_xor & -full_xor).bit_length() - 1
            assert rank.first_changed_bit == j
            assert rank.cancellation_depth == ((p - 1) & -(p - 1)).bit_length() - 1
            assert rank.first_flip_direction == (
                "OFF" if (primorial >> j) & 1 else "ON"
            )
            assert rank.residue == p % rank.modulus
            assert rank.rank_queries > 0
            assert leaf.rank_queries == 0
            assert owner.pending_frames == 0
        finally:
            owner.close()
        assert owner.ledger.nodes == owner.ledger.entries == 0


def test_no_witness_and_incomplete_or_corrupt_source_fail_closed() -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7))
    try:
        owner.validate_consecutive_prefix()
        # 8,9 are both composite, no prime in this interval.
        assert owner.first_survivor_xor_bellman(8, 10, mode="rank") is None
        assert owner.first_survivor_xor_bellman(8, 10, mode="leaf") is None
        with pytest.raises(ValueError, match="follow the admitted"):
            owner.first_survivor_xor_bellman(7, 15)
        with pytest.raises(ValueError, match="complete prime-root"):
            owner.first_survivor_xor_bellman(8, 1_000)
    finally:
        owner.close()
    forgery = CoprimeRankDAG((2, 3, 5, 11))
    try:
        with pytest.raises(ValueError, match="consecutive"):
            forgery.first_survivor_xor_bellman(12, 20)
    finally:
        forgery.close()


def test_bellman_budget_refusal_releases_query_work() -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7, 11, 13))
    try:
        owner.validate_consecutive_prefix()
        owner.max_work = owner.work + 1
        with pytest.raises(ValueError, match="work budget"):
            owner.first_survivor_xor_bellman(14, 27, mode="leaf")
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()
    assert owner.ledger.nodes == owner.ledger.entries == 0


def test_bellman_requires_authenticated_rank_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7, 11))
    try:
        owner.validate_consecutive_prefix()
        # Force a corrupted source verification before the Bellman action.
        monkeypatch.setattr(
            owner,
            "_validate_factor_source",
            lambda: (_ for _ in ()).throw(RuntimeError("source changed")),
        )
        with pytest.raises(RuntimeError, match="source changed"):
            owner.first_survivor_xor_bellman(12, 23)
    finally:
        owner.close()


def test_bellman_interrupted_work_leaves_ledger_consistent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner = CoprimeRankDAG((2, 3, 5, 7, 11, 13))
    try:
        owner.validate_consecutive_prefix()

        def interrupted(_work: int = 0) -> None:
            raise ArithmeticError("candidate inspection interrupted")

        monkeypatch.setattr(owner, "charge", interrupted)
        with pytest.raises(ArithmeticError, match="interrupted"):
            owner.first_survivor_xor_bellman(14, 27, mode="leaf")
        assert all(row.accounting_delta == 0 for row in owner.ledger.inventory())
    finally:
        owner.close()
    assert owner.ledger.entries == owner.ledger.nodes == 0
