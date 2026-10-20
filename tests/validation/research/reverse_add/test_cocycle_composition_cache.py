"""Authority and resource boundaries for finite temporal composition reuse."""

from collections.abc import Callable, MutableMapping
from dataclasses import replace
from typing import TypeVar, cast

import pytest

from devtools.experiments.reverse_add.cocycle_temporal import (
    CocycleAction,
    CocycleCompositionEntry,
    CocycleCompositionKey,
    CocycleTemporalAuditSnapshot,
)
from devtools.experiments.reverse_add.cocycle_temporal_payload_audit import (
    audit_cocycle_temporal_payloads,
)
from devtools.verification.reverse_cocycle_context import BoundedReverseCocycle
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.support.private_attributes import private_test_attribute


def _work(context: BoundedReverseCocycle) -> tuple[int, ...]:
    counters = context.bits.ledger.counters
    return tuple(
        counters.get(name, 0)
        for name in (
            "semantic_bit_batch_composition_evaluations",
            "semantic_bit_composition_evaluations",
            "semantic_bit_substitution_frames",
            "semantic_bit_batch_restriction_evaluations",
            "semantic_function_ite_frames",
        )
    )


def _cache_key(before: CocycleAction, after: CocycleAction) -> CocycleCompositionKey:
    return CocycleCompositionKey(
        before.ports,
        before.outputs,
        before.cocycles,
        before.admissible,
        before.events,
        after.ports,
        after.outputs,
        after.cocycles,
        after.admissible,
        after.events,
    )


_K = TypeVar("_K")
_V = TypeVar("_V")


def _forensic_memo(
    snapshot: OwnedMemoAuditSnapshot[_K, _V],
) -> MutableMapping[_K, _V]:
    """Write through a fixed-cost audit snapshot only in corruption cases."""
    if snapshot.dynamic_cost:
        raise AssertionError("forensic writes require a fixed-cost memo")
    return cast(MutableMapping[_K, _V], snapshot.container)


def test_warm_pair_performs_no_semantic_construction_work() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    before = _work(context)
    result = context.temporal.compose(primitive, primitive)
    cold = _work(context)
    assert cold[0] == before[0] + 1
    assert cold[3] == before[3] + 1

    warm = context.temporal.compose(primitive, primitive)
    assert warm is result
    assert _work(context) == cold
    assert context.temporal.temporal_compositions == 1
    assert context.temporal.temporal_composition_cache_hits == 1


def test_equal_actions_with_distinct_event_counts_have_distinct_cache_entries() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    shifted = replace(primitive, events=2)
    assert shifted == primitive

    ordinary = context.temporal.compose(primitive, primitive)
    shifted_result = context.temporal.compose(shifted, primitive)
    assert ordinary.events == 2
    assert shifted_result.events == 3
    assert len(context.temporal.audit_snapshot().composition_cache.container) == 2
    assert context.temporal.temporal_composition_cache_hits == 0


def test_foreign_and_stale_actions_fail_before_cache_publication() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    foreign = BoundedReverseCocycle(2).compile_primitive()
    before = context.bits.ledger.snapshot()

    with pytest.raises(ValueError):
        context.temporal.compose(primitive, foreign)
    stale = FactoredFunctionID(
        primitive.outputs[0].owner,
        primitive.outputs[0].kind,
        len(context.bits.nodes),
    )
    with pytest.raises(ValueError):
        context.temporal.compose(
            replace(primitive, outputs=(stale, *primitive.outputs[1:])),
            primitive,
        )

    after = context.bits.ledger.snapshot()
    assert len(context.temporal.audit_snapshot().composition_cache.container) == 0
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )


def test_valid_shape_cache_substitution_is_rejected() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    result = context.temporal.compose(primitive, primitive)
    key = _cache_key(primitive, primitive)
    snapshot = context.temporal.audit_snapshot()
    entry_value = snapshot.composition_cache.payload_view[key]
    assert type(entry_value) is CocycleCompositionEntry
    entry = entry_value
    assert entry.result is result

    cache = _forensic_memo(snapshot.composition_cache)
    cache[key] = CocycleCompositionEntry(key, entry.entry_id, primitive)
    with pytest.raises(ValueError, match="cache|publication|events"):
        context.temporal.compose(primitive, primitive)


def test_cache_cap_evicts_the_oldest_complete_key_and_reconciles_entries() -> None:
    context = BoundedReverseCocycle(1)
    primitive = context.compile_primitive()
    temporal = context.temporal
    ledger = context.bits.ledger
    initial_snapshot = temporal.audit_snapshot()
    limit = initial_snapshot.composition_cache_limit
    assert limit == 1024
    keys = tuple(
        _cache_key(replace(primitive, events=event), primitive)
        for event in range(1, limit + 1)
    )
    for event in range(1, limit + 1):
        temporal.compose(replace(primitive, events=event), primitive)
    snapshot = temporal.audit_snapshot()
    assert len(snapshot.composition_cache.container) == limit
    assert len(snapshot.composition_seals.container) == limit
    inventory = _assert_composition_inventory(ledger, snapshot)

    temporal.compose(replace(primitive, events=limit + 1), primitive)
    snapshot = temporal.audit_snapshot()
    assert len(snapshot.composition_cache.container) == limit
    assert len(snapshot.composition_seals.container) == limit
    assert keys[0] not in snapshot.composition_cache.container
    assert keys[0] not in snapshot.composition_seals.container
    assert keys[-1] in snapshot.composition_cache.container
    inventory = _assert_composition_inventory(ledger, snapshot)
    assert inventory[snapshot.composition_cache.owner].accounting_delta == 0
    assert inventory[snapshot.composition_seals.owner].accounting_delta == 0


def test_failed_cold_composition_leaves_no_cache_or_semantic_publication() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    ledger = context.bits.ledger
    before = ledger.snapshot()
    lengths = (
        len(context.bits.functions.nodes),
        len(context.bits.nodes),
        len(context.bits.composition_audit_snapshot().container),
        len(context.temporal.audit_snapshot().composition_cache.container),
    )
    ledger.tighten_limits(max_nodes=ledger.nodes, max_cache_entries=ledger.entries)

    with pytest.raises(BlockContextBudgetExceeded):
        context.temporal.compose(primitive, primitive)

    after = ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert lengths == (
        len(context.bits.functions.nodes),
        len(context.bits.nodes),
        len(context.bits.composition_audit_snapshot().container),
        len(context.temporal.audit_snapshot().composition_cache.container),
    )


def test_paired_query_memo_eviction_allows_clean_cold_recomposition() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    first = context.temporal.compose(primitive, primitive)
    snapshot = context.temporal.audit_snapshot()
    assert len(snapshot.composition_cache.container) == 1
    assert len(snapshot.composition_seals.container) == 1

    evicted = context.bits.ledger.evict_query_memos()
    assert snapshot.composition_cache.owner in evicted
    assert snapshot.composition_seals.owner in evicted
    snapshot = context.temporal.audit_snapshot()
    assert len(snapshot.composition_cache.container) == 0
    assert len(snapshot.composition_seals.container) == 0

    second = context.temporal.compose(primitive, primitive)
    assert second == first
    snapshot = context.temporal.audit_snapshot()
    assert len(snapshot.composition_cache.container) == 1
    assert len(snapshot.composition_seals.container) == 1
    assert all(row.accounting_delta == 0 for row in context.bits.ledger.inventory())


def test_missing_cache_counterpart_is_rejected() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    context.temporal.compose(primitive, primitive)
    key = _cache_key(primitive, primitive)
    snapshot = context.temporal.audit_snapshot()
    del _forensic_memo(snapshot.composition_seals)[key]

    with pytest.raises(ValueError, match="incomplete"):
        context.temporal.compose(primitive, primitive)
    assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid


def test_cache_insertion_failure_removes_preceding_seal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    snapshot = context.temporal.audit_snapshot()
    cache = cast(
        OwnedMemo[CocycleCompositionKey, CocycleCompositionEntry],
        snapshot.composition_cache_identity,
    )
    original = cast(
        Callable[[OwnedMemo[object, object], object, object], None],
        private_test_attribute(OwnedMemo, "__setitem__"),
    )

    def fail_cache_insert(
        memo: OwnedMemo[object, object], key: object, value: object
    ) -> None:
        if memo is cache:
            raise RuntimeError("injected composition-cache failure")
        original(memo, key, value)

    monkeypatch.setattr(OwnedMemo, "__setitem__", fail_cache_insert)
    with pytest.raises(RuntimeError, match="injected"):
        context.temporal.compose(primitive, primitive)
    snapshot = context.temporal.audit_snapshot()
    assert len(snapshot.composition_cache.container) == 0
    assert len(snapshot.composition_seals.container) == 0
    assert all(row.accounting_delta == 0 for row in context.bits.ledger.inventory())


def test_composition_cache_is_independently_resource_auditable() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    context.temporal.compose(primitive, primitive)
    assert not audit_cocycle_temporal_payloads(context.bits.ledger).invalid
    assert audit_registered_payloads(context.bits.ledger).forbidden_future_payloads > 0
    assert all(row.accounting_delta == 0 for row in context.bits.ledger.inventory())


def test_audit_rejects_unexpected_arena_payload() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    context.temporal.compose(primitive, primitive)
    attributes = vars(context.temporal)
    attributes["_future_endpoint"] = 1 << 128
    try:
        assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid
    finally:
        del attributes["_future_endpoint"]


def test_audit_rejects_corrupted_cache_entry_and_seal() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    context.temporal.compose(primitive, primitive)
    key = _cache_key(primitive, primitive)
    snapshot = context.temporal.audit_snapshot()
    entry_value = snapshot.composition_cache.payload_view[key]
    seal_value = snapshot.composition_seals.payload_view[key]
    assert type(entry_value) is CocycleCompositionEntry
    assert type(seal_value) is tuple
    entry = entry_value
    old_seal = cast(tuple[object, ...], seal_value)

    cache = _forensic_memo(snapshot.composition_cache)
    seals = _forensic_memo(snapshot.composition_seals)
    cache[key] = CocycleCompositionEntry(key, entry.entry_id, primitive)
    try:
        assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid
    finally:
        cache[key] = entry

    seals[key] = (*old_seal[:-1], 0)
    try:
        assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid
    finally:
        seals[key] = old_seal


def test_cache_limit_is_an_exact_integer_policy() -> None:
    snapshot = BoundedReverseCocycle(1).temporal.audit_snapshot()
    assert type(snapshot.composition_cache_limit) is int
    assert snapshot.composition_cache_limit == 1024


def _assert_composition_inventory(
    ledger: ResourceLedger,
    snapshot: CocycleTemporalAuditSnapshot,
) -> dict[int, ResourceInventory]:
    inventory = {row.owner: row for row in ledger.inventory()}
    assert inventory[snapshot.composition_cache.owner].entries == 1024
    assert inventory[snapshot.composition_seals.owner].entries == 1024
    return inventory
