"""Certified behavior occurrence bindings use the shared result owner."""

from __future__ import annotations

from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.tiles.tile_behavior_memo import (
    behavior_binding_key,
    lookup_behavior_classification,
    publish_behavior_classification,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    CompletedBehaviorClassification,
)
from tests.support.assertions import assert_publication_state_unchanged
from tests.support.tile_kernel import (
    make_tile_from_symbols,
    make_tile_runtime,
    powered_runtime,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.behavior.future_behavior import FutureBehaviorClassID
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileLease
    from number_compiler.resources.ledger import ResourceLedger


def behavior_binding_fixture() -> tuple[
    ResourceLedger,
    PrimitiveTileKernelAdapter,
    CompletedResultArena,
    TileLease,
    BehaviorBindingKey,
    FutureBehaviorClassID,
]:
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    engine = CausalTileEngine(scheduler)
    blank = adapter.primitive_law(primitive).blank
    source = make_tile_from_symbols(tiles, adapter, primitive, (blank,) * 4)
    key = engine.composite_key(
        action,
        source.tile,
        engine.initial_state(action, 0),
        engine.initial_state(action, 1),
    )
    assert key is not None
    quotient = adapter.kernels.behavioral_quotient(adapter.action_record(action).kernel)
    profile, behavior = adapter.quotients.admit_quiescent_blank(quotient)
    return (
        ledger,
        adapter,
        scheduler.results,
        source,
        behavior_binding_key(key, profile),
        behavior,
    )


def test_behavior_binding_warm_hit_is_read_only_and_skips_proof(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, adapter, results, source, key, behavior = behavior_binding_fixture()
    try:
        published = publish_behavior_classification(results, key, behavior)
        before = ledger.snapshot()

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm behavior hit repeated a semantic proof")

        monkeypatch.setattr(adapter.kernels, "behavioral_quotient", forbidden)
        assert lookup_behavior_classification(results, key) == published
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert after.counters[
            "future_behavior_binding_early_hits"
        ] > before.counters.get(
            "future_behavior_binding_early_hits",
            0,
        )
        assert after.counters["future_behavior_binding_requests"] == (
            before.counters.get("future_behavior_binding_requests", 0) + 1
        )
    finally:
        source.close()


def test_behavior_binding_seal_rejects_mutated_class() -> None:
    _ledger, _adapter, results, source, key, behavior = behavior_binding_fixture()
    try:
        publish_behavior_classification(results, key, behavior)
        record = results.audit_snapshot().memo[key]
        assert type(record) is CompletedBehaviorClassification
        object.__setattr__(record, "_publication_snapshot", ())
        with pytest.raises(ValueError, match="publication metadata was modified"):
            lookup_behavior_classification(results, key)
    finally:
        source.close()


def test_behavior_binding_retires_with_exact_input() -> None:
    _ledger, _adapter, results, source, key, behavior = behavior_binding_fixture()
    publish_behavior_classification(results, key, behavior)
    assert key in results.audit_snapshot().memo
    source.close()
    assert key not in results.audit_snapshot().memo
    assert not results.audit_snapshot().reverse


def test_behavior_binding_detaches_caller_key_before_publication() -> None:
    _ledger, _adapter, results, source, key, behavior = behavior_binding_fixture()
    publish_behavior_classification(results, key, behavior)
    stored = next(iter(results.audit_snapshot().memo))
    assert stored is not key
    assert type(stored) is BehaviorBindingKey and stored.request is not key.request
    object.__setattr__(
        key.request,
        "ports",
        (key.request.ports[0] + 1, *key.request.ports[1:]),
    )
    source.close()
    assert not results.audit_snapshot().memo
    assert not results.audit_snapshot().reverse


def test_behavior_binding_publication_is_atomic_at_exhausted_budget() -> None:
    ledger, _adapter, results, source, key, behavior = behavior_binding_fixture()
    try:
        ledger.max_cache_entries = ledger.entries
        memo_before = dict(results.audit_snapshot().memo)
        reverse_before = dict(results.audit_snapshot().reverse)
        accounting = ledger.entries, ledger.nodes
        with pytest.raises(BlockContextBudgetExceeded):
            publish_behavior_classification(results, key, behavior)
        assert_publication_state_unchanged(
            memo_before,
            reverse_before,
            accounting,
            memo_after=results.audit_snapshot().memo,
            reverse_after=results.audit_snapshot().reverse,
            accounting_after=(ledger.entries, ledger.nodes),
        )
    finally:
        source.close()


def test_behavior_binding_rejects_foreign_profile_before_mutation() -> None:
    ledger, _adapter, results, source, key, _behavior = behavior_binding_fixture()
    _ledger2, _tiles2, adapter2, primitive2, _scheduler2 = make_tile_runtime(
        BaseBlockEffect(3)
    )
    quotient2 = adapter2.kernels.behavioral_quotient(
        adapter2.action_record(primitive2).kernel,
    )
    foreign_profile, _foreign_behavior = adapter2.quotients.admit_quiescent_blank(
        quotient2,
    )
    malformed = BehaviorBindingKey(key.request, foreign_profile)
    try:
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="different arena"):
            lookup_behavior_classification(results, malformed)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
    finally:
        source.close()


def test_public_warm_behavior_point_and_width_skip_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.behavior.quiescent_admission as quotient_module
    import number_compiler.hashlife.tiles.tile_behavior_memo as behavior_memo
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel

    _ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    action = adapter.power(primitive, 8)
    blank = adapter.primitive_law(primitive).blank
    with (
        make_tile_from_symbols(tiles, adapter, primitive, (blank,) * 8) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        assert application.point(0) == blank
        nodes = len(tiles.audit_snapshot().nodes)
        scheduler.ledger.max_cache_entries = scheduler.ledger.entries + 64

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm behavior observation rebuilt causal output")

        monkeypatch.setattr(behavior_memo, "_validate_blank_proof", forbidden)
        monkeypatch.setattr(quotient_module, "certify_quiescent_blank", forbidden)
        monkeypatch.setattr(tiles, "leaf", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        monkeypatch.setattr(PrimitiveKernel, "emit", forbidden)
        assert application.point(7) == blank
        assert application.width() == 0
        assert len(tiles.audit_snapshot().nodes) == nodes


def test_new_behavior_admission_fails_before_semantic_publication_at_zero_budget() -> (
    None
):
    ledger, tiles, adapter, primitive, scheduler, action, blank = powered_runtime(
        BaseBlockEffect(3), 4
    )
    with (
        make_tile_from_symbols(tiles, adapter, primitive, (blank,) * 4) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        assert not adapter.quotients.future_behavior_store_counts()[0]
        ledger.max_cache_entries = ledger.entries
        with pytest.raises(BlockContextBudgetExceeded):
            application.point(0)
        assert not adapter.quotients.future_behavior_store_counts()[0]
        assert not adapter.quotients.future_behavior_store_counts()[2]
