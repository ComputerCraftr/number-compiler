"""Hot action validation reuses an authenticated append-only prime prefix."""

import pytest

from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.successor_action import PrimeSuccessorActionArena


def test_action_accesses_do_not_copy_or_rescan_an_unchanged_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=10_000, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 7, parent_depth=3)

    def forbidden(_rank: CoprimeRankDAG) -> tuple[int, ...]:
        raise AssertionError("hot prime action copied the complete factor prefix")

    monkeypatch.setattr(CoprimeRankDAG, "primes", property(forbidden))
    try:
        action = arena.prefix(96)
        expected = sum(all(value % p for p in (2, 3, 5, 7)) for value in range(1, 97))
        for _ in range(20):
            assert arena.rank_before(action, 0, 96) == expected
            arena.node(action)
            arena.port_effect(arena.base, 0)
        assert (
            dag.ledger.counters.get("prime_successor_prefix_validation_factors", 0) == 0
        )
        dag.append_consecutive_factor(11)
        for _ in range(20):
            assert arena.rank_before(action, 0, 96) == expected
        assert dag.ledger.counters["prime_successor_prefix_validation_factors"] == 4
        dag._primes._data[1] = 11
        with pytest.raises(RuntimeError, match="parent source binding"):
            arena.node(action)
        # An unissued mutation is rejected before any stale numerical memo can
        # be used to recertify the corrupted prefix.
        assert dag.ledger.counters["prime_successor_prefix_validation_factors"] == 4
    finally:
        arena.close()
        dag.close()


def test_closed_or_replaced_factor_authority_cannot_reuse_prefix_validation() -> None:
    dag = CoprimeRankDAG((2, 3, 5, 7), max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 7, parent_depth=3)
    foreign = CoprimeRankDAG((2, 3, 5, 7), max_work=100_000)
    original = dag._primes
    try:
        object.__setattr__(dag, "_primes", foreign._primes)
        with pytest.raises(ValueError, match="source authority"):
            arena.node(arena.base)
        object.__setattr__(dag, "_primes", original)
        dag.close()
        with pytest.raises(RuntimeError, match="closed"):
            arena.node(arena.base)
    finally:
        object.__setattr__(dag, "_primes", original)
        arena.close()
        dag.close()
        foreign.close()


def test_new_arena_and_warm_counts_reject_mutated_issued_prefix() -> None:
    dag = CoprimeRankDAG((2, 3, 5, 7), max_work=100_000)
    try:
        dag.validate_consecutive_prefix(4)
        dag.count(128)
        dag.count_progression(128, 11, 0)
        dag._primes._data[2] = 4
        with pytest.raises(RuntimeError, match="prime factor source changed"):
            PrimeSuccessorActionArena(dag, 4, parent_depth=2)
        with pytest.raises(RuntimeError, match="prime factor source changed"):
            dag.validate_consecutive_prefix(4)
        with pytest.raises(RuntimeError, match="prime factor source changed"):
            dag.count(128)
        with pytest.raises(RuntimeError, match="prime factor source changed"):
            dag.count_progression(128, 11, 0)
        with pytest.raises(RuntimeError, match="prime factor source changed"):
            dag.append_factor(11)
    finally:
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0
