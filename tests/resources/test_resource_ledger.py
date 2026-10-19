"""Resource limits fail before allocation and retain an auditable owner inventory."""

from collections.abc import Iterator
from copy import copy
from typing import TypeGuard, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
    ResourceScope,
)
from number_compiler.resources.owned_memo import (
    DynamicMemoValue,
    OwnedMemoAuditPayloadView,
)
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.stores import LedgerDict, TrackedDict
from tests.support.assertions import assert_rejected_atomically


def _is_reservation_store(value: object) -> TypeGuard[TrackedDict[object, object]]:
    return type(value) is TrackedDict and all(
        type(key) is LedgerReservation for key in value
    )


def test_owner_name_batch_preflight_is_exact_distinct_and_nonmutating() -> None:
    ledger = ResourceLedger()
    ledger.require_fresh_owner_names(("first", "second"))
    with pytest.raises(TypeError, match="tuple"):
        ledger.require_fresh_owner_names(cast(tuple[str, ...], ["first"]))
    with pytest.raises(TypeError, match="strings"):
        ledger.require_fresh_owner_names(cast(tuple[str, ...], ("first", 1)))
    with pytest.raises(ValueError, match="distinct"):
        ledger.require_fresh_owner_names(("same", "same"))
    with pytest.raises(ValueError, match="nonempty"):
        ledger.require_fresh_owner_names(("",))

    ledger.register("taken", "TEST_OWNER")
    before = ledger.owner_count
    with pytest.raises(ValueError, match="already registered"):
        ledger.require_fresh_owner_names(("fresh", "taken"))
    assert ledger.owner_count == before


@pytest.mark.parametrize("dimension", ["entries", "nodes"])
def test_zero_budget_rejects_before_any_mutation(dimension: str) -> None:
    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    owner = ledger.register("program", "ACTION_PROGRAM")
    assert_rejected_atomically(
        ledger,
        lambda: ledger.reserve(
            owner, entries=int(dimension == "entries"), nodes=int(dimension == "nodes")
        ),
        BlockContextBudgetExceeded,
    )


def test_combined_reservation_is_atomic_and_owner_release_is_checked() -> None:
    ledger = ResourceLedger(max_nodes=2, max_cache_entries=3)
    first = ledger.register("source", "EXACT_SOURCE", ResourceScope.INDEX_OWNED)
    second = ledger.register("program", "ACTION_PROGRAM")
    ledger.reserve(first, entries=1, nodes=1)
    assert_rejected_atomically(
        ledger,
        lambda: ledger.reserve(second, entries=1, nodes=2),
        BlockContextBudgetExceeded,
    )
    ledger.reserve(second, entries=2, nodes=1)
    assert (ledger.entries, ledger.nodes) == (3, 2)
    with pytest.raises(ValueError):
        ledger.release(first, entries=2)
    assert (ledger.entries, ledger.nodes) == (3, 2)
    ledger.release(second, entries=2, nodes=1)
    assert (ledger.entries, ledger.nodes) == (1, 1)
    assert (ledger.peak_entries, ledger.peak_nodes) == (3, 2)


def test_single_owner_reservation_matches_one_item_batch() -> None:
    single = ResourceLedger(max_nodes=5, max_cache_entries=4)
    batch = ResourceLedger(max_nodes=5, max_cache_entries=4)
    single_owner = single.register("single", "SUMMARY")
    batch_owner = batch.register("single", "SUMMARY")

    single.reserve(single_owner, entries=2, nodes=3)
    batch.reserve_many(((batch_owner, 2, 3),))

    assert single.snapshot() == batch.snapshot()


@pytest.mark.parametrize(
    ("entries", "nodes", "error_type"),
    (
        (-1, 0, ValueError),
        (True, 0, TypeError),
        (0, -1, ValueError),
        (0, False, TypeError),
    ),
)
def test_single_owner_reservation_matches_batch_validation(
    entries: int, nodes: int, error_type: type[Exception]
) -> None:
    single = ResourceLedger()
    batch = ResourceLedger()
    single_owner = single.register("single", "SUMMARY")
    batch_owner = batch.register("single", "SUMMARY")
    single_before = single.snapshot()
    batch_before = batch.snapshot()

    with pytest.raises(error_type) as single_error:
        single.reserve(single_owner, entries=entries, nodes=nodes)
    with pytest.raises(error_type) as batch_error:
        batch.reserve_many(((batch_owner, entries, nodes),))

    assert str(single_error.value) == str(batch_error.value)
    assert single.snapshot() == single_before
    assert batch.snapshot() == batch_before


def test_single_owner_reservation_matches_disposed_and_tightened_owner_checks() -> None:
    single = ResourceLedger(max_nodes=5, max_cache_entries=5)
    batch = ResourceLedger(max_nodes=5, max_cache_entries=5)
    single_owner = single.register("single", "SUMMARY")
    batch_owner = batch.register("single", "SUMMARY")
    single.reserve(single_owner, entries=1, nodes=1)
    batch.reserve_many(((batch_owner, 1, 1),))
    single.tighten_limits(max_nodes=1, max_cache_entries=5)
    batch.tighten_limits(max_nodes=1, max_cache_entries=5)
    single_before = single.snapshot()
    batch_before = batch.snapshot()

    with pytest.raises(BlockContextBudgetExceeded) as single_error:
        single.reserve(single_owner, nodes=1)
    with pytest.raises(BlockContextBudgetExceeded) as batch_error:
        batch.reserve_many(((batch_owner, 0, 1),))

    assert str(single_error.value) == str(batch_error.value)
    assert single.snapshot() == single_before
    assert batch.snapshot() == batch_before

    single.release(single_owner, entries=1, nodes=1)
    batch.release(batch_owner, entries=1, nodes=1)
    single.mark_disposed(single_owner)
    batch.mark_disposed(batch_owner)
    with pytest.raises(RuntimeError, match="disposed") as single_disposed:
        single.reserve(single_owner)
    with pytest.raises(RuntimeError, match="disposed") as batch_disposed:
        batch.reserve_many(((batch_owner, 0, 0),))
    assert str(single_disposed.value) == str(batch_disposed.value)


def test_inventory_counts_registered_owners_and_typed_roots_once() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("summary", "TRANSFER_SUMMARY")
    assert ledger.register("summary", "TRANSFER_SUMMARY") == owner
    with pytest.raises(ValueError):
        ledger.register("summary", "EXACT_ENDPOINT")
    handle = ArenaHandle(ArenaToken("query"), "summary", 0)
    ledger.reserve(owner, entries=1, nodes=1)
    ledger.register_root(owner, handle)
    ledger.register_root(owner, handle)
    ledger.bump("port_queries", 3)
    snapshot = ledger.snapshot()
    assert snapshot.inventory[0].roots == (handle,)
    assert sum(item.entries for item in snapshot.inventory) == snapshot.entries == 1
    assert sum(item.nodes for item in snapshot.inventory) == snapshot.nodes == 1
    ledger.bump("port_queries")
    assert snapshot.counters == {"port_queries": 3}
    ledger.unregister_root(owner, handle)
    assert not ledger.inventory()[0].roots


def test_owner_inventory_does_not_visit_unrelated_resolvers() -> None:
    ledger = ResourceLedger()
    selected = ledger.register("selected", "TRANSFER_SUMMARY")
    unrelated = ledger.register("unrelated", "TRANSFER_SUMMARY")
    ledger.reserve(selected, entries=1, nodes=2)
    expected = ledger.inventory()[selected]

    def forbidden() -> tuple[ArenaHandle, ...]:
        raise AssertionError("single-owner audit visited an unrelated source")

    ledger.register_container(unrelated, [], roots=forbidden)
    assert ledger.inventory_owner(selected) == expected
    with pytest.raises(AssertionError, match="unrelated source"):
        ledger.inventory()


def test_invalid_owner_and_negative_operations_do_not_change_ledger() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("source", "EXACT_SOURCE")
    before = ledger.snapshot()
    for invalid in (-1, owner + 1):
        with pytest.raises(ValueError):
            ledger.reserve(invalid)
    with pytest.raises(ValueError):
        ledger.reserve(owner, entries=-1)
    with pytest.raises(ValueError):
        ledger.release(owner, nodes=-1)
    with pytest.raises(ValueError):
        ledger.bump("queries", -1)
    assert ledger.snapshot() == before


def test_reservation_fast_validation_preserves_error_order_and_messages() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("source", "EXACT_SOURCE")
    ledger.max_nodes = False
    ledger.max_cache_entries = -1

    with pytest.raises(TypeError, match="node budget must be an integer"):
        ledger.reserve(owner, entries=-1, nodes=False)

    ledger.max_nodes = None
    ledger.max_cache_entries = None
    with pytest.raises(ValueError, match="cache entry count must be >= 0"):
        ledger.reserve(owner, entries=-1, nodes=False)


def test_owned_memo_accounts_updates_eviction_and_clear() -> None:
    ledger = ResourceLedger(max_nodes=2, max_cache_entries=2)
    owner = ledger.register("memo", "ACTION_PROGRAM")
    memo: OwnedMemo[int, str] = OwnedMemo(ledger, owner, nodes_per_entry=1)
    memo[1] = "first"
    memo[1] = "replacement"
    assert memo.setdefault(1, "unused") == "replacement"
    assert memo.setdefault(2, "second") == "second"
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        memo[3] = "rejected"
    assert 3 not in memo and ledger.snapshot() == before
    assert dict(memo.items()) == {1: "replacement", 2: "second"}
    assert memo.pop(1) == "replacement"
    assert (ledger.entries, ledger.nodes) == (1, 1)
    assert ledger.inventory()[0].accounting_delta == 0
    assert tuple(ledger.iter_payloads()) == ((owner, 2), (owner, "second"))
    memo.clear()
    assert (ledger.entries, ledger.nodes) == (0, 0)


def test_dynamic_memo_adopts_exact_workspace_charge() -> None:
    ledger = ResourceLedger(max_nodes=8, max_cache_entries=2)
    source = ledger.register("memo-workspace", "WORKSPACE")
    target = ledger.register("memo-retained", "ACTION_PROGRAM")
    reservation = LedgerReservation(ledger, source)
    reservation.reserve(entries=1, nodes=8)
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, target, node_cost=lambda _key, value: len(value)
    )

    memo.adopt_reserved("root", (1, 2), reservation)

    assert memo["root"] == (1, 2)
    assert ledger.entries == ledger.peak_entries == 1
    assert ledger.nodes == ledger.peak_nodes == 8
    inventory = ledger.inventory()
    assert inventory[source].nodes == 5
    assert inventory[target].nodes == 3
    assert inventory[source].entries == 0
    assert inventory[target].entries == 1
    reservation.close()
    assert ledger.nodes == 3
    memo.clear()
    assert ledger.nodes == ledger.entries == 0


def _assert_adoption_refusal_is_atomic(
    memo: OwnedMemo[str, tuple[int, ...]],
    key: str,
    reservation: LedgerReservation,
) -> None:
    before = memo.ledger.snapshot()
    with pytest.raises(ValueError, match="exceeds this reservation"):
        memo.adopt_reserved(key, (1, 2), reservation)
    assert memo.ledger.snapshot() == before


def test_dynamic_memo_adoption_rejects_unowned_or_duplicate_credit() -> None:
    ledger = ResourceLedger(max_nodes=8, max_cache_entries=4)
    source = ledger.register("memo-adoption-source", "WORKSPACE")
    target = ledger.register("memo-adoption-target", "ACTION_PROGRAM")
    foreign_ledger = ResourceLedger(max_nodes=8)
    foreign_owner = foreign_ledger.register("foreign", "WORKSPACE")
    foreign = LedgerReservation(foreign_ledger, foreign_owner)
    foreign.reserve(nodes=8)
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, target, node_cost=lambda _key, value: len(value)
    )
    with pytest.raises(ValueError, match="different ledgers"):
        memo.adopt_reserved("new", (1, 2), foreign)
    foreign.close()

    ledger.reserve(source, nodes=3)
    untracked = LedgerReservation(ledger, source)
    copied = copy(untracked)
    with pytest.raises(RuntimeError, match="closed or is foreign"):
        copied.transfer_to(target, nodes=1)
    with pytest.raises(AttributeError, match="binding is immutable"):
        untracked._ledger = foreign_ledger
    with pytest.raises(AttributeError):
        untracked._nodes = 3
    _assert_adoption_refusal_is_atomic(memo, "new", untracked)
    ledger.release(source, nodes=3)
    with pytest.raises(ValueError, match="closing the owner's reservations"):
        ledger.mark_disposed(source)
    untracked.close()

    reservation = LedgerReservation(ledger, source)
    reservation.reserve(entries=1, nodes=2)
    _assert_adoption_refusal_is_atomic(memo, "new", reservation)
    reservation.reserve(nodes=4)
    memo["existing"] = (9,)
    before_duplicate = ledger.snapshot()
    with pytest.raises(KeyError, match="new key"):
        memo.adopt_reserved("existing", (1, 2), reservation)
    assert ledger.snapshot() == before_duplicate
    reservation.close()
    memo.clear()
    assert ledger.nodes == ledger.entries == 0


def test_dynamic_memo_adoption_rolls_back_on_base_exception(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger(max_nodes=8, max_cache_entries=2)
    source = ledger.register("memo-rollback-source", "WORKSPACE")
    target = ledger.register("memo-rollback-target", "ACTION_PROGRAM")
    reservation = LedgerReservation(ledger, source)
    reservation.reserve(entries=1, nodes=8)
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, target, node_cost=lambda _key, value: len(value)
    )
    original_setitem = LedgerDict[object, object].__setitem__

    def insert_then_cancel(
        store: LedgerDict[object, object], key: object, value: object
    ) -> None:
        original_setitem(store, key, value)
        raise KeyboardInterrupt("interrupted after insertion")

    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_cancel)
    with pytest.raises(KeyboardInterrupt, match="after insertion"):
        memo.adopt_reserved("root", (1, 2), reservation)
    assert "root" not in memo
    assert ledger.inventory()[source].nodes == 8
    assert ledger.inventory()[target].nodes == 0
    assert ledger.inventory()[source].entries == 1
    assert ledger.inventory()[target].entries == 0
    reservation.close()
    assert ledger.nodes == ledger.entries == 0


def test_owned_memo_charges_dynamic_payload_nodes_atomically() -> None:
    ledger = ResourceLedger(max_nodes=8, max_cache_entries=3)
    owner = ledger.register("dynamic-memo", "ACTION_PROGRAM")
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger,
        owner,
        node_cost=lambda key, value: len(key) + len(value),
    )
    memo["a"] = (1, 2)
    assert (ledger.entries, ledger.nodes) == (1, 4)
    assert ledger.inventory()[owner].accounting_delta == 0
    memo["a"] = (1,)
    assert (ledger.entries, ledger.nodes) == (1, 3)
    memo["b"] = (3, 4)
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        memo["c"] = (5, 6)
    assert ledger.snapshot() == before and "c" not in memo
    assert memo.pop("a") == (1,)
    assert (ledger.entries, ledger.nodes) == (1, 4)
    assert ledger.inventory()[owner].accounting_delta == 0
    memo.clear()
    assert (ledger.entries, ledger.nodes) == (0, 0)


def test_dynamic_memo_cost_metadata_uses_its_registered_mapping() -> None:
    ledger = ResourceLedger(max_nodes=16, max_cache_entries=4)
    owner = ledger.register("audited-dynamic-memo", "ACTION_PROGRAM")
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, owner, node_cost=lambda key, value: len(key) + len(value)
    )
    memo["a"] = (1, 2)

    assert memo["a"] == (1, 2)
    assert not hasattr(memo, "_costs")
    assert audit_execution_ownership(ledger).violations == ()
    assert tuple(ledger.iter_payloads()) == (
        (owner, "a"),
        (owner, (1, 2)),
    )

    memo["a"] = (3,)
    assert ledger.inventory()[owner].accounting_delta == 0
    assert memo.pop("a") == (3,)
    assert (ledger.entries, ledger.nodes) == (0, 0)


def test_owned_memo_rejects_invalid_dynamic_node_cost_without_mutation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("invalid-dynamic-memo", "ACTION_PROGRAM")
    memo: OwnedMemo[int, str] = OwnedMemo(
        ledger, owner, node_cost=lambda _key, _value: -1
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="payload node cost"):
        memo[0] = "value"
    assert ledger.snapshot() == before and len(memo) == 0


def test_higher_runtime_environment_nodes_reconcile_on_clear() -> None:
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimeValueArena,
    )

    ledger = ResourceLedger()
    values = RuntimeValueArena(ledger)
    assert values.intern_environment(-1, 0, 1) == 0
    snapshot = ledger.snapshot()
    assert snapshot.nodes == 1
    assert sum(item.observed_nodes or 0 for item in snapshot.inventory) == 1
    values.clear()
    snapshot = ledger.snapshot()
    assert snapshot.entries == snapshot.nodes == 0
    assert sum(item.observed_nodes or 0 for item in snapshot.inventory) == 0


def test_independent_inventory_detects_unreserved_container_mutation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("deliberate-bad-container", "SUMMARY")
    container: dict[int, int] = {}
    ledger.register_container(owner, container)
    container[1] = 9
    inventory = ledger.inventory()[0]
    assert inventory.entries == 0 and inventory.observed_entries == 1
    assert inventory.accounting_delta == 1


def test_multi_owner_reservation_rejects_without_changing_peaks() -> None:
    ledger = ResourceLedger(max_cache_entries=1)
    first = ledger.register("nodes", "ACTION_PROGRAM")
    second = ledger.register("interner", "ACTION_INTERNER")
    before = assert_rejected_atomically(
        ledger,
        lambda: ledger.reserve_many(((first, 1, 1), (second, 1, 0))),
        BlockContextBudgetExceeded,
    )
    with pytest.raises(ValueError):
        ledger.reserve_many(((first, 1, 1), (999, 0, 0)))
    assert ledger.snapshot() == before
    ledger.reserve_many(((first, 1, 1), (second, 0, 0)))
    assert (ledger.entries, ledger.nodes) == (1, 1)


def test_multi_owner_reservation_rechecks_limits_after_arbitrary_iteration() -> None:
    ledger = ResourceLedger(max_nodes=2, max_cache_entries=2)
    owner = ledger.register("nodes", "ACTION_PROGRAM")
    before = ledger.snapshot()

    def reservations() -> Iterator[tuple[int, int, int]]:
        yield owner, 1, 1
        ledger.max_nodes = False

    with pytest.raises(TypeError, match="node budget"):
        ledger.reserve_many(reservations())

    assert ledger.snapshot() == before


def test_multi_owner_reservation_rejects_disposed_owner_before_atomic_commit() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("disposed-mid-reservation", "ACTION_PROGRAM")

    def reservations() -> Iterator[tuple[int, int, int]]:
        yield owner, 1, 1
        ledger.mark_disposed(owner)

    with pytest.raises(RuntimeError, match="disposed"):
        ledger.reserve_many(reservations())

    inventory = ledger.inventory()[owner]
    assert inventory.disposed
    assert (ledger.entries, ledger.nodes) == (0, 0)
    assert (inventory.entries, inventory.nodes) == (0, 0)


def test_resource_reassignment_is_net_bounded_and_atomic() -> None:
    ledger = ResourceLedger(max_nodes=2, max_cache_entries=4)
    workspace = ledger.register("workspace", "semantic_function_workspace")
    nodes = ledger.register("canonical-nodes", "semantic_function")
    keys = ledger.register("canonical-keys", "semantic_function_interner")
    ledger.reserve(workspace, entries=4, nodes=2)
    ledger.reassign_many(
        ((workspace, 4, 2),),
        ((nodes, 2, 2), (keys, 2, 0)),
    )
    assert (ledger.entries, ledger.nodes) == (4, 2)
    inventory = {item.name: item for item in ledger.inventory()}
    assert (inventory["workspace"].entries, inventory["workspace"].nodes) == (0, 0)
    assert (
        inventory["canonical-nodes"].entries,
        inventory["canonical-nodes"].nodes,
    ) == (
        2,
        2,
    )


def test_resource_reassignment_rechecks_mutable_budget_after_iteration() -> None:
    ledger = ResourceLedger(max_nodes=2, max_cache_entries=2)
    source = ledger.register("source", "semantic_function_workspace")
    target = ledger.register("target", "semantic_function")
    ledger.reserve(source, entries=1, nodes=1)
    before = ledger.snapshot()

    def releases() -> Iterator[tuple[int, int, int]]:
        yield source, 1, 1
        ledger.max_nodes = False

    with pytest.raises(TypeError, match="node budget"):
        ledger.reassign_many(releases(), ((target, 1, 1),))

    assert ledger.snapshot() == before


def test_resource_reassignment_rechecks_staged_owners_before_commit() -> None:
    ledger = ResourceLedger()
    source = ledger.register("source", "semantic_function_workspace")
    target = ledger.register("target", "semantic_function")
    ledger.reserve(source, entries=1, nodes=1)

    def reservations() -> Iterator[tuple[int, int, int]]:
        yield target, 1, 1
        ledger.mark_disposed(target)

    with pytest.raises(RuntimeError, match="disposed"):
        ledger.reassign_many(((source, 1, 1),), reservations())

    inventory = {row.name: row for row in ledger.inventory()}
    assert (ledger.entries, ledger.nodes) == (1, 1)
    assert (inventory["source"].entries, inventory["source"].nodes) == (1, 1)
    assert inventory["target"].disposed
    assert (inventory["target"].entries, inventory["target"].nodes) == (0, 0)


def test_failed_resource_reassignment_changes_no_account_or_peak() -> None:
    ledger = ResourceLedger(max_nodes=1, max_cache_entries=2)
    workspace = ledger.register("workspace", "semantic_function_workspace")
    target = ledger.register("target", "semantic_function")
    ledger.reserve(workspace, entries=1, nodes=1)
    before = assert_rejected_atomically(
        ledger,
        lambda: ledger.reassign_many(((workspace, 1, 1),), ((target, 3, 2),)),
        BlockContextBudgetExceeded,
    )
    with pytest.raises(ValueError):
        ledger.reassign_many(((workspace, 2, 1),), ())
    assert ledger.snapshot() == before


def test_query_eviction_releases_actual_payloads_but_not_canonical_programs() -> None:
    import weakref

    class Payload:
        pass

    ledger = ResourceLedger()
    program_owner = ledger.register("program", "action_program")
    programs: OwnedMemo[int, str] = OwnedMemo(ledger, program_owner, nodes_per_entry=1)
    programs[0] = "canonical program"
    query_owner = ledger.register("query", "transfer_summary")
    queries: OwnedMemo[int, object] = OwnedMemo(
        ledger, query_owner, nodes_per_entry=1, evictable=True
    )
    payload = Payload()
    retained = weakref.ref(payload)
    queries[0] = payload
    del payload
    assert retained() is not None
    assert ledger.evict_query_memos() == (query_owner,)
    assert retained() is None
    assert dict(programs) == {0: "canonical program"}
    assert (ledger.entries, ledger.nodes) == (1, 1)
    assert ledger.inventory()[query_owner].accounting_delta == 0
    with pytest.raises(ValueError):
        OwnedMemo(ledger, ledger.register("invalid", "action_program"), evictable=True)


def test_arithmetic_observations_count_measured_width_and_reject_large_results() -> (
    None
):
    ledger = ResourceLedger()
    assert ledger.observe_arithmetic(7) == 7
    assert ledger.observe_arithmetic((1 << 64) - 1) == (1 << 64) - 1
    assert ledger.counters["bounded_limb_operations"] == 2
    assert ledger.counters["maximum_arithmetic_bits"] == 64
    with pytest.raises(ArithmeticError):
        ledger.observe_arithmetic(1 << 64)
    assert ledger.counters["unbounded_arithmetic_observations"] == 1
    assert ledger.counters["maximum_arithmetic_bits"] == 65


def test_dispose_releases_payload_and_rejects_even_warm_access() -> None:
    import weakref

    class Payload:
        pass

    ledger = ResourceLedger()
    owner = ledger.register("query", "query_memo")
    memo: OwnedMemo[int, object] = OwnedMemo(
        ledger, owner, evictable=True, composition_entries=True
    )
    payload = Payload()
    saved = weakref.ref(payload)
    memo[0] = payload
    del payload
    memo.dispose()
    memo.dispose()
    assert saved() is None
    inventory = ledger.inventory()[owner]
    assert inventory.disposed and inventory.entries == inventory.observed_entries == 0
    assert inventory.composition_entries == 0
    assert tuple(ledger.iter_payloads()) == ()
    with pytest.raises(RuntimeError):
        memo.get(0)
    with pytest.raises(RuntimeError):
        memo[0] = object()
    with pytest.raises(RuntimeError):
        memo.pop(0, None)
    with pytest.raises(RuntimeError):
        ledger.reserve(owner, entries=1)
    ledger.evict_query_memos()


def test_owned_memo_audit_payload_view_is_read_only_and_counter_neutral_after_close() -> (
    None
):
    ledger = ResourceLedger()
    owner = ledger.register("closed-audit", "query_memo")
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, owner, node_cost=lambda _key, value: len(value)
    )
    memo["kept"] = (2, 3)
    before = ledger.snapshot()

    live_view = memo.audit_payload_view()
    assert live_view["kept"] == (2, 3)
    assert live_view.backing_store_identity is memo.audit_snapshot().container
    assert ledger.snapshot() == before

    memo.dispose()
    after_close = ledger.snapshot()
    closed_view = memo.audit_payload_view()
    assert len(closed_view) == 0
    assert tuple(closed_view) == ()
    assert closed_view.backing_store_identity is memo.audit_snapshot().container
    assert ledger.snapshot() == after_close


def test_dynamic_memo_audit_view_rejects_malformed_cost_wrapper() -> None:
    malformed: dict[str, DynamicMemoValue[str] | str] = {
        "bad": "payload without cost metadata"
    }
    view = OwnedMemoAuditPayloadView(malformed, dynamic_cost=True)

    with pytest.raises(TypeError, match="invalid cost metadata"):
        _ = view["bad"]


def test_owning_term_and_ledger_lifetime_does_not_pin_unowned_arenas() -> None:
    import gc
    import weakref

    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 16)
    term.completed_q19_occurrence()
    workspace = term.published_workspace
    assert workspace is not None
    ledger = weakref.ref(term.resource_ledger)
    scheduler = weakref.ref(workspace.scheduler)
    actions = weakref.ref(workspace.actions)
    workspace_owner = weakref.ref(workspace)
    del workspace, term
    gc.collect()
    assert ledger() is None
    assert scheduler() is None
    assert actions() is None
    assert workspace_owner() is None


def test_container_identity_has_one_owner_and_same_owner_can_upgrade_resolver() -> None:
    ledger = ResourceLedger()
    first = ledger.register("first", "query_memo")
    second = ledger.register("second", "query_memo")
    container: dict[int, int] = {}
    ledger.register_container(first, container)
    assert_rejected_atomically(
        ledger,
        lambda: ledger.register_container(
            second, container, payloads=lambda: (object(),)
        ),
        ValueError,
        match="multiple resource owners",
    )
    assert tuple(ledger.iter_payloads()) == ()
    ledger.reserve(first, entries=1)
    container[0] = 7
    ledger.register_container(first, container, payloads=container.values)
    assert tuple(ledger.iter_payloads()) == ((first, 7),)
    assert ledger.inventory()[first].accounting_delta == 0
    assert ledger.inventory()[second].observed_entries is None


def test_disposed_owner_cannot_register_payloads_or_roots() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("disposed", "query_memo")
    container: dict[int, int] = {}
    ledger.register_container(owner, container, payloads=container.values)
    ledger.mark_disposed(owner)
    before = ledger.snapshot()
    for candidate in (container, {0: 7}):
        with pytest.raises(RuntimeError, match="disposed"):
            ledger.register_container(owner, candidate, payloads=candidate.values)
        assert ledger.snapshot() == before
    with pytest.raises(RuntimeError, match="disposed"):
        ledger.register_root(owner, ArenaHandle(ArenaToken("closed"), "summary", 0))
    assert ledger.snapshot() == before
    assert tuple(ledger.iter_payloads()) == ()


def test_payload_audit_cache_is_reused_and_invalidated_by_store_mutations() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    ledger = ResourceLedger()
    owner = ledger.register("audited", "query_memo")
    store: LedgerDict[object, object]
    store = ledger.make_dict(owner)
    first = audit_registered_payloads(ledger, fresh=False)
    assert audit_registered_payloads(ledger, fresh=False) is first

    ledger.reserve(owner, entries=1)
    store[0] = "bounded"
    second = audit_registered_payloads(ledger, fresh=False)
    assert second is not first
    assert audit_registered_payloads(ledger, fresh=False) is second

    # Adversarial tests intentionally bypass the public store wrapper. The
    # tracked backing container still invalidates previously cached evidence.
    version = ledger.mutation_version
    backing = object.__getattribute__(store, "_data")
    assert isinstance(backing, TrackedDict)
    backing[0] = b"future-payload"
    assert ledger.mutation_version > version
    third = audit_registered_payloads(ledger, fresh=False)
    assert third is not second
    assert third.forbidden_future_payloads > 0


def test_ownership_audit_cache_is_invalidated_by_new_execution_roots() -> None:
    from number_compiler.resources.ownership import audit_execution_ownership

    class Root:
        def __init__(self) -> None:
            self.unowned: dict[int, int] = {}

    ledger = ResourceLedger()
    first = audit_execution_ownership(ledger)
    assert audit_execution_ownership(ledger) is first
    root = Root()
    ledger.register_execution_root(root)
    second = audit_execution_ownership(ledger)
    assert second is not first
    assert second.unregistered_containers == 1


def test_reservation_bookkeeping_audits_mutable_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ownership import audit_execution_ownership

    ledger = ResourceLedger()
    owner = ledger.register("reservation-audit", "WORKSPACE")
    reservation = LedgerReservation(ledger, owner)
    assert audit_execution_ownership(ledger).violations == ()

    reservation_store = object.__getattribute__(ledger, "_reservations")
    assert _is_reservation_store(reservation_store)
    assert reservation in reservation_store
    with monkeypatch.context() as patch:
        patch.setitem(reservation_store, reservation, (owner, 0, []))
        audit = audit_execution_ownership(ledger)
        assert any("_reservations.value" in item.path for item in audit.violations)

    reservation.close()


def test_reservation_close_rejects_foreign_and_spoofed_handles() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("reservation-close", "WORKSPACE")
    reservation = LedgerReservation(ledger, owner)
    reservation.reserve(entries=1, nodes=1)
    foreign = ResourceLedger()
    foreign_owner = foreign.register("foreign-reservation-close", "WORKSPACE")
    foreign_reservation = LedgerReservation(foreign, foreign_owner)

    assert reservation.belongs_to(ledger)
    assert not foreign_reservation.belongs_to(ledger)
    assert foreign_reservation.resource_ledger is foreign
    with pytest.raises(TypeError, match="exact tracker"):
        ledger._close_reservation(object())
    with pytest.raises(ValueError, match="another ledger"):
        ledger._close_reservation(foreign_reservation)
    assert ledger._reservation_state(reservation) == (owner, 1, 1)
    reservation.close()
    reservation.close()
    assert (ledger.entries, ledger.nodes) == (0, 0)
    with pytest.raises(RuntimeError, match="closed or is foreign"):
        reservation.transfer_to(owner, entries=1)
    foreign_reservation.close()


def test_public_metrics_reuse_audits_until_a_registered_store_mutates() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    class Root:
        def __init__(self, store: object) -> None:
            self.store = store

    ledger = ResourceLedger()
    owner = ledger.register("metric-audit-store", "query_memo")
    store: LedgerDict[object, object]
    store = ledger.make_dict(owner)
    root = Root(store)
    ledger.register_execution_root(root)

    first = collect_ledger_metrics(ledger)
    first_payload = ledger.cached_payload_audit()
    first_ownership = ledger.cached_ownership_audit()
    assert first_payload is not None
    assert first_ownership is not None

    second = collect_ledger_metrics(ledger, audit_payloads=False)
    assert ledger.cached_payload_audit() is first_payload
    assert ledger.cached_ownership_audit() is first_ownership
    assert second.resource_inventory == first.resource_inventory

    ledger.reserve(owner, entries=1)
    store[0] = "bounded"
    assert ledger.cached_payload_audit() is None
    assert ledger.cached_ownership_audit() is None
    third = collect_ledger_metrics(ledger, audit_payloads=False)
    assert ledger.cached_payload_audit() is None
    assert ledger.cached_ownership_audit() is not first_ownership
    assert third.resource_ledger_entries == first.resource_ledger_entries + 1

    refreshed = collect_ledger_metrics(ledger)
    assert ledger.cached_payload_audit() is not first_payload
    assert refreshed.resource_audit_complete == 1


def test_explicit_live_root_audit_bypasses_public_metrics_cache() -> None:
    from number_compiler.resources.ownership import audit_execution_ownership

    class Root:
        injected: object = None

    ledger = ResourceLedger()
    root = Root()
    ledger.register_execution_root(root)
    cached = audit_execution_ownership(ledger, fresh=False)
    assert cached.unregistered_containers == 0
    root.injected = {}
    assert audit_execution_ownership(ledger).unregistered_containers == 1


@pytest.mark.parametrize("alias", [True, 0.0, "0"])
def test_root_resolver_rejects_integer_alias_before_inventory(alias: object) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("resolved-roots", "query_memo")
    container: list[object] = []
    handle = ArenaHandle(ArenaToken("root"), "summary", 0)
    object.__setattr__(handle, "local_id", alias)
    ledger.register_container(owner, container, roots=lambda: (handle,))
    before = (ledger.entries, ledger.nodes)
    with pytest.raises(ValueError, match="malformed scoped handle"):
        ledger.inventory()
    assert (ledger.entries, ledger.nodes) == before


def test_mutated_registered_root_rejects_before_warm_inventory() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("registered-root", "query_memo")
    handle = ArenaHandle(ArenaToken("root"), "summary", 0)
    ledger.register_root(owner, handle)
    assert ledger.inventory()[owner].roots == (handle,)
    object.__setattr__(handle, "local_id", True)
    with pytest.raises(ValueError, match="malformed scoped handle"):
        ledger.inventory()
