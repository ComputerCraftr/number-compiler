"""Authority and resource boundaries for finite temporal composition reuse."""

from dataclasses import replace

import pytest

from number_compiler.resources.ledger import ResourceLedger, ResourceInventory

from devtools.experiments.reverse_add.cocycle_temporal import (
    CocycleAction,
    CocycleTemporalArena,
    _CompositionEntry,
    _CompositionKey,
)
from devtools.experiments.reverse_add.cocycle_temporal_payload_audit import (
    audit_cocycle_temporal_payloads,
)
from devtools.verification.reverse_cocycle_context import BoundedReverseCocycle
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.payload_audit import audit_registered_payloads


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


def _cache_key(before: CocycleAction, after: CocycleAction) -> _CompositionKey:
    return _CompositionKey(
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
    assert len(context.temporal._composition_cache) == 2
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
    assert len(context.temporal._composition_cache) == 0
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
    entry = context.temporal._composition_cache[key]
    assert entry.result is result

    context.temporal._composition_cache._data[key] = _CompositionEntry(
        key, entry.entry_id, primitive
    )
    with pytest.raises(ValueError, match="cache|publication|events"):
        context.temporal.compose(primitive, primitive)


def test_cache_cap_evicts_the_oldest_complete_key_and_reconciles_entries() -> None:
    context = BoundedReverseCocycle(1)
    primitive = context.compile_primitive()
    temporal = context.temporal
    assert temporal._COMPOSITION_CACHE_LIMIT == 1024
    ledger = context.bits.ledger
    keys = tuple(
        _cache_key(replace(primitive, events=event), primitive)
        for event in range(1, temporal._COMPOSITION_CACHE_LIMIT + 1)
    )
    for key in keys:
        entry = _CompositionEntry(
            key,
            temporal._next_composition_entry,
            replace(primitive, events=key.before_events + key.after_events),
        )
        temporal._next_composition_entry += 1
        temporal._composition_seals[key] = temporal._entry_seal(entry)
        temporal._composition_cache[key] = entry
    assert len(temporal._composition_cache) == temporal._COMPOSITION_CACHE_LIMIT
    assert len(temporal._composition_seals) == temporal._COMPOSITION_CACHE_LIMIT
    inventory = _assert_composition_inventory(ledger, temporal)

    temporal.compose(replace(primitive, events=1025), primitive)
    assert len(temporal._composition_cache) == temporal._COMPOSITION_CACHE_LIMIT
    assert len(temporal._composition_seals) == temporal._COMPOSITION_CACHE_LIMIT
    assert keys[0] not in temporal._composition_cache
    assert keys[0] not in temporal._composition_seals
    assert keys[-1] in temporal._composition_cache
    inventory = _assert_composition_inventory(ledger, temporal)
    assert inventory[temporal._composition_cache.owner].accounting_delta == 0
    assert inventory[temporal._composition_seals.owner].accounting_delta == 0


def test_failed_cold_composition_leaves_no_cache_or_semantic_publication() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    ledger = context.bits.ledger
    before = ledger.snapshot()
    lengths = (
        len(context.bits.functions.nodes),
        len(context.bits.nodes),
        len(context.bits._compositions),
        len(context.temporal._composition_cache),
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
        len(context.bits._compositions),
        len(context.temporal._composition_cache),
    )


def test_paired_query_memo_eviction_allows_clean_cold_recomposition() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    first = context.temporal.compose(primitive, primitive)
    assert len(context.temporal._composition_cache) == 1
    assert len(context.temporal._composition_seals) == 1

    evicted = context.bits.ledger.evict_query_memos()
    assert context.temporal._composition_cache.owner in evicted
    assert context.temporal._composition_seals.owner in evicted
    assert len(context.temporal._composition_cache) == 0
    assert len(context.temporal._composition_seals) == 0

    second = context.temporal.compose(primitive, primitive)
    assert second == first
    assert len(context.temporal._composition_cache) == 1
    assert len(context.temporal._composition_seals) == 1
    assert all(row.accounting_delta == 0 for row in context.bits.ledger.inventory())


def test_missing_cache_counterpart_is_rejected() -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    context.temporal.compose(primitive, primitive)
    key = _cache_key(primitive, primitive)
    del context.temporal._composition_seals[key]

    with pytest.raises(ValueError, match="incomplete"):
        context.temporal.compose(primitive, primitive)
    assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid


def test_cache_insertion_failure_removes_preceding_seal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    cache = context.temporal._composition_cache
    original = OwnedMemo.__setitem__

    def fail_cache_insert(
        memo: OwnedMemo[object, object], key: object, value: object
    ) -> None:
        if memo is cache:
            raise RuntimeError("injected composition-cache failure")
        original(memo, key, value)

    monkeypatch.setattr(OwnedMemo, "__setitem__", fail_cache_insert)
    with pytest.raises(RuntimeError, match="injected"):
        context.temporal.compose(primitive, primitive)
    assert len(context.temporal._composition_cache) == 0
    assert len(context.temporal._composition_seals) == 0
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
    entry = context.temporal._composition_cache[key]
    old_seal = context.temporal._composition_seals[key]

    context.temporal._composition_cache._data[key] = _CompositionEntry(
        key, entry.entry_id, primitive
    )
    try:
        assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid
    finally:
        context.temporal._composition_cache._data[key] = entry

    context.temporal._composition_seals._data[key] = (*old_seal[:-1], 0)
    try:
        assert audit_cocycle_temporal_payloads(context.bits.ledger).invalid
    finally:
        context.temporal._composition_seals._data[key] = old_seal


def test_cache_limit_is_an_exact_integer_policy() -> None:
    assert type(CocycleTemporalArena._COMPOSITION_CACHE_LIMIT) is int
    assert CocycleTemporalArena._COMPOSITION_CACHE_LIMIT == 1024


def _assert_composition_inventory(
    ledger: ResourceLedger,
    temporal: CocycleTemporalArena,
) -> dict[int, ResourceInventory]:
    inventory = {row.owner: row for row in ledger.inventory()}
    assert inventory[temporal._composition_cache.owner].entries == 1024
    assert inventory[temporal._composition_seals.owner].entries == 1024
    return inventory
