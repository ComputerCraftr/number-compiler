"""A failed child cleanup must not strand a process-cache authority."""

from contextlib import closing
from typing import Never

import pytest

from number_compiler.projection import lazy_radix
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import ProcessCache
from number_compiler.sequences.antihydra import mahler_source_actions
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.prime import select
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.partial_successor_image import (
    PrimePartialSuccessorQuery,
)


@pytest.mark.parametrize("child", ("query", "dag", "scheduler", "neither"))
def test_prime_teardown_releases_lease_after_child_failure(
    child: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    cache = ProcessCache()
    monkeypatch.setattr(select, "get_process_cache", lambda: cache)
    owner = select.PrimePrefixRank(
        max_states=10_000, max_work=100_000, max_stages=100, shared_cache=True
    )
    assert owner.count_prime_interval(2, 30) == 10
    query = owner.partial_successor_query
    assert isinstance(query, PrimePartialSuccessorQuery)
    assert cache.stats().active_leases == 1

    def failed_close() -> Never:
        raise RuntimeError("child cleanup failed")

    with monkeypatch.context() as patch:
        if child != "neither":
            if child == "scheduler":
                patch.setattr(query._scheduler, "dispose_source_images", failed_close)
            else:
                patch.setattr(
                    query if child == "query" else owner.dag, "close", failed_close
                )
            with pytest.raises(RuntimeError, match="child cleanup failed"):
                owner.close()
            if child == "scheduler":
                assert query._arena is not None and query._arena._closed
        else:
            with closing(owner):
                assert owner.count_prime_interval(2, 10) == 4
    assert cache.stats().active_leases == 0
    owner.close()
    assert owner.dag.ledger.entries == owner.dag.ledger.nodes == 0


@pytest.mark.parametrize("lease_failure", (False, True))
def test_mahler_teardown_releases_lease_after_record_disposal_failure(
    lease_failure: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache()
    monkeypatch.setattr(mahler_source_actions, "get_process_cache", lambda: cache)
    consumer = mahler_source_actions.MahlerOccurrenceConsumer(
        ResourceLedger(), ANTIHYDRA_ARITHMETIC_LAW, shared_cache=True
    )
    assert cache.stats().active_leases == 1

    def failed_disposal() -> Never:
        raise RuntimeError("record disposal failed")

    def failed_lease() -> Never:
        raise RuntimeError("lease close failed")

    with monkeypatch.context() as patch:
        patch.setattr(consumer.records, "dispose", failed_disposal)
        if lease_failure:
            assert consumer.lease is not None
            patch.setattr(consumer.lease, "close", failed_lease)
        expected = "lease close failed" if lease_failure else "record disposal failed"
        with pytest.raises(RuntimeError, match=expected) as caught, consumer:
            pass
        if lease_failure:
            assert isinstance(caught.value.__context__, RuntimeError)
            assert str(caught.value.__context__) == "record disposal failed"
    assert cache.stats().active_leases == int(lease_failure)
    consumer.close()
    assert cache.stats().active_leases == 0
    assert consumer.ledger.entries == consumer.ledger.nodes == 0


def test_prime_dag_disposes_remaining_stores_when_first_cleanup_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    dag = CoprimeRankDAG((2, 3, 5), max_states=10_000, max_work=100_000)
    dag.count(100)

    def failed_disposal() -> Never:
        raise RuntimeError("progression disposal failed")

    with monkeypatch.context() as patch:
        patch.setattr(dag.progression_memo, "dispose", failed_disposal)
        with pytest.raises(RuntimeError, match="progression disposal failed"):
            dag.close()
    rows = {row.owner: row for row in dag.ledger.inventory()}
    assert rows[dag.memo.owner].disposed
    assert rows[dag._progression_inverses.owner].disposed
    assert rows[dag._factor_owner].disposed
    dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_failed_radix_constructor_retires_unpublished_allocations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(27, 1)
    ledger = term.audit_snapshot().ledger
    before = ledger.entries, ledger.nodes
    roots = tuple(ledger.iter_execution_roots())
    original = lazy_radix.RadixProjection.__init__

    def fail_after_allocation(
        self: lazy_radix.RadixProjection,
        radix: int,
        width: int,
        ledger: ResourceLedger,
        microblocks: MicroblockCache | None = None,
        *,
        width_is_upper_bound: bool = False,
    ) -> Never:
        original(
            self,
            radix,
            width,
            ledger,
            microblocks,
            width_is_upper_bound=width_is_upper_bound,
        )
        raise RuntimeError("radix setup failed")

    with monkeypatch.context() as patch:
        patch.setattr(lazy_radix.RadixProjection, "__init__", fail_after_allocation)
        with pytest.raises(RuntimeError, match="radix setup failed"):
            lazy_radix.collatz_radix_digit(term, 3, 0)
    assert (ledger.entries, ledger.nodes) == before
    assert tuple(ledger.iter_execution_roots()) == roots
    audit_source = term.radix_projection_audit_source(ledger)
    assert audit_source is not None
    assert 3 not in audit_source.projections
    assert lazy_radix.collatz_radix_digit(term, 3, 0) == 82 % 3
