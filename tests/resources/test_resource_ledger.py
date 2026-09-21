"""Resource limits fail before allocation and retain an auditable owner inventory."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict


@pytest.mark.parametrize("dimension", ["entries", "nodes"])
def test_zero_budget_rejects_before_any_mutation(dimension: str) -> None:
    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    owner = ledger.register("program", "ACTION_PROGRAM")
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        ledger.reserve(
            owner, entries=int(dimension == "entries"), nodes=int(dimension == "nodes")
        )
    assert ledger.snapshot() == before


def test_combined_reservation_is_atomic_and_owner_release_is_checked() -> None:
    ledger = ResourceLedger(max_nodes=2, max_cache_entries=3)
    first = ledger.register("source", "EXACT_SOURCE", "INDEX_OWNED")
    second = ledger.register("program", "ACTION_PROGRAM")
    ledger.reserve(first, entries=1, nodes=1)
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        ledger.reserve(second, entries=1, nodes=2)
    assert ledger.snapshot() == before
    ledger.reserve(second, entries=2, nodes=1)
    assert (ledger.entries, ledger.nodes) == (3, 2)
    with pytest.raises(ValueError):
        ledger.release(first, entries=2)
    assert (ledger.entries, ledger.nodes) == (3, 2)
    ledger.release(second, entries=2, nodes=1)
    assert (ledger.entries, ledger.nodes) == (1, 1)
    assert (ledger.peak_entries, ledger.peak_nodes) == (3, 2)


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
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        ledger.reserve_many(((first, 1, 1), (second, 1, 0)))
    assert ledger.snapshot() == before
    with pytest.raises(ValueError):
        ledger.reserve_many(((first, 1, 1), (999, 0, 0)))
    assert ledger.snapshot() == before
    ledger.reserve_many(((first, 1, 1), (second, 0, 0)))
    assert (ledger.entries, ledger.nodes) == (1, 1)


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


def test_failed_resource_reassignment_changes_no_account_or_peak() -> None:
    ledger = ResourceLedger(max_nodes=1, max_cache_entries=2)
    workspace = ledger.register("workspace", "semantic_function_workspace")
    target = ledger.register("target", "semantic_function")
    ledger.reserve(workspace, entries=1, nodes=1)
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        ledger.reassign_many(
            ((workspace, 1, 1),),
            ((target, 3, 2),),
        )
    assert ledger.snapshot() == before
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


def test_owning_term_and_ledger_lifetime_does_not_pin_unowned_arenas() -> None:
    import gc
    import weakref

    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 16)
    workspace = term._source_workspace()
    ledger = weakref.ref(term._ledger)
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
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="multiple resource owners"):
        ledger.register_container(second, container, payloads=lambda: (object(),))
    assert ledger.snapshot() == before
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
    first = audit_registered_payloads(ledger)
    assert audit_registered_payloads(ledger) is first

    ledger.reserve(owner, entries=1)
    store[0] = "bounded"
    second = audit_registered_payloads(ledger)
    assert second is not first
    assert audit_registered_payloads(ledger) is second

    # Adversarial tests intentionally bypass the public store wrapper. The
    # tracked backing container still invalidates previously cached evidence.
    version = ledger.mutation_version
    store._data[0] = b"future-payload"
    assert ledger.mutation_version > version
    third = audit_registered_payloads(ledger)
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

    second = collect_ledger_metrics(ledger)
    assert ledger.cached_payload_audit() is first_payload
    assert ledger.cached_ownership_audit() is first_ownership
    assert second.resource_inventory == first.resource_inventory

    ledger.reserve(owner, entries=1)
    store[0] = "bounded"
    assert ledger.cached_payload_audit() is None
    assert ledger.cached_ownership_audit() is None
    third = collect_ledger_metrics(ledger)
    assert ledger.cached_payload_audit() is not first_payload
    assert ledger.cached_ownership_audit() is not first_ownership
    assert third.resource_ledger_entries == first.resource_ledger_entries + 1


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
