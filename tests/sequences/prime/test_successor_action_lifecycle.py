"""Failure cleanup for query-owned prime successor action stores."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import LedgerSnapshot, OwnedMemo, ResourceLedger
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.partial_successor_image import (
    PrimePartialSuccessorQuery,
)
from number_compiler.sequences.prime.successor_action import PrimeSuccessorActionArena
from tests.support.prime_actions import partial_prime_arena


def _assert_prior_inventory_unchanged(
    before: LedgerSnapshot, after: LedgerSnapshot
) -> None:
    before_rows = before.inventory
    assert after.inventory[: len(before_rows)] == before_rows
    created = after.inventory[len(before_rows) :]
    assert len(created) == 3
    assert all(row.disposed and row.entries == row.nodes == 0 for row in created)


def test_constructor_budget_failure_releases_every_created_store() -> None:
    dag = CoprimeRankDAG((2, 3), max_states=100, max_work=100_000)
    try:
        dag.validate_fresh_successor(5)
        before = dag.ledger.snapshot()
        retained = before.entries - dag.factor_count
        dag.max_states = retained + 3
        with pytest.raises(ValueError, match="prime state budget"):
            PrimeSuccessorActionArena(dag, 5)
        after = dag.ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        _assert_prior_inventory_unchanged(before, after)

        dag.max_states = retained + 100
        _assert_successor_close_restores(dag, before)
    finally:
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_constructor_naming_does_not_build_a_full_inventory(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=100, max_work=100_000)
    dag.validate_fresh_successor(5)
    before = dag.ledger.snapshot()

    def forbidden_inventory() -> Never:
        raise AssertionError("arena naming traversed the resource inventory")

    try:
        with monkeypatch.context() as patch:
            patch.setattr(dag.ledger, "inventory", forbidden_inventory)
            arena = PrimeSuccessorActionArena(dag, 5)
            arena.close()
        assert (dag.ledger.entries, dag.ledger.nodes) == (
            before.entries,
            before.nodes,
        )
    finally:
        dag.close()


def test_stage_scheduler_construction_failure_closes_the_published_action_arena(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=100, max_work=100_000)
    dag.validate_consecutive_prefix()
    query = PrimePartialSuccessorQuery(dag)
    before = dag.ledger.snapshot()

    def fail_source_only(
        _scheduler_type: type[TileScheduler], _ledger: ResourceLedger
    ) -> TileScheduler:
        raise RuntimeError("injected source scheduler construction failure")

    try:
        with monkeypatch.context() as patch:
            patch.setattr(TileScheduler, "source_only", classmethod(fail_source_only))
            with pytest.raises(RuntimeError, match="injected source scheduler"):
                query.count_primes(2, 5, 2)
        after = dag.ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        created = after.inventory[len(before.inventory) :]
        assert len(created) == 3
        assert all(row.disposed and row.entries == row.nodes == 0 for row in created)
    finally:
        query.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_production_interval_query_can_replace_a_completed_prime_stage() -> None:
    dag = CoprimeRankDAG((2, 3, 5), max_states=10_000, max_work=100_000)
    query = PrimePartialSuccessorQuery(dag)
    try:
        assert query.count_primes(2, 8, 2) == 4
        previous = partial_prime_arena(query)
        assert previous is not None
        assert query.count_primes(2, 24, 3) == 9
        assert previous.audit_snapshot().closed
        assert partial_prime_arena(query) is not previous
        assert query.count_primes(2, 8, 2) == 4
    finally:
        query.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


@pytest.mark.parametrize(
    ("lower", "upper", "depth", "expected"),
    ((2, 4, 1, 2), (5, 6, 2, 1), (5, 6, 3, 1), (6, 7, 2, 0), (7, 8, 2, 1)),
)
def test_partial_stage_restores_only_the_factors_it_removed(
    lower: int, upper: int, depth: int, expected: int
) -> None:
    dag = CoprimeRankDAG((2, 3, 5), max_states=10_000, max_work=100_000)
    query = PrimePartialSuccessorQuery(dag)
    try:
        assert query.count_primes(lower, upper, depth) == expected
    finally:
        query.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


@pytest.mark.parametrize("failed_publication", range(1, 5))
def test_constructor_publication_failure_rolls_back_only_its_own_allocations(
    monkeypatch: pytest.MonkeyPatch,
    failed_publication: int,
) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=100, max_work=100_000)
    dag.validate_fresh_successor(5)
    before = dag.ledger.snapshot()
    first_arena_owner = len(before.inventory)
    original = OwnedMemo[object, object].__setitem__
    publications = 0

    def fail_selected_publication(
        self: OwnedMemo[object, object], key: object, value: object
    ) -> None:
        nonlocal publications
        if self.ledger is dag.ledger and self.owner >= first_arena_owner:
            publications += 1
            if publications == failed_publication:
                raise RuntimeError("injected prime action publication failure")
        original(self, key, value)

    with monkeypatch.context() as patch:
        patch.setattr(OwnedMemo, "__setitem__", fail_selected_publication)
        with pytest.raises(RuntimeError, match="injected prime action publication"):
            PrimeSuccessorActionArena(dag, 5)

    after = dag.ledger.snapshot()
    try:
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        _assert_prior_inventory_unchanged(before, after)
        _assert_successor_close_restores(dag, before)
    finally:
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def _assert_successor_close_restores(
    dag: CoprimeRankDAG, before: LedgerSnapshot
) -> None:
    arena = PrimeSuccessorActionArena(dag, 5)
    arena.close()
    assert (dag.ledger.entries, dag.ledger.nodes) == (before.entries, before.nodes)
