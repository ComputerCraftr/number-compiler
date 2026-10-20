"""Output-independent causal bindings use the shared result memo."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import (
    ExactReverseOutputFrame,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    primitive_interface_payload,
)
from number_compiler.hashlife.execution.tile_causal_results import PrimitiveCausalPorts
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    causal_interface_key,
    lookup_causal_interface,
    publish_causal_interface,
    validate_published_causal_interface_value,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    CompletedInterfaceResult,
    PoweredResultKey,
    causal_interface_snapshot,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_publication_state_unchanged
from tests.support.tile_kernel import make_tile_runtime, make_tile_runtime_source

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_structures import (
        LocalInterfaceID,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileArena, TileLease
    from number_compiler.resources.ledger import ResourceLedger


def causal_interface_binding() -> tuple[
    ResourceLedger,
    TileArena,
    CompletedResultArena,
    TileLease,
    CausalInterfaceKey,
    CausalInterfacePayload,
]:
    ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        BaseBlockEffect(3), (1,)
    )
    ports = PrimitiveCausalPorts(*adapter.initial_ports(action))
    wiring = adapter.wiring(action)
    key = causal_interface_key(
        PoweredResultKey(action, source.tile, ports.ports, wiring)
    )
    payload = primitive_interface_payload(
        scheduler.results,
        action,
        source.tile,
        ports,
        wiring,
        TemporalCocycle(),
    )
    return ledger, tiles, scheduler.results, source, key, payload


def test_causal_interface_binding_preserves_complete_bounded_result() -> None:
    ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        assert lookup_causal_interface(results, key) is None
        assert publish_causal_interface(results, key, payload) == payload
        before = ledger.snapshot()
        assert lookup_causal_interface(results, key) == payload
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert after.counters["causal_interface_result_early_hits"] == 1
    finally:
        source.close()


def test_warm_interface_parent_answers_before_child_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        ledger,
        _unused_tiles_binding,
        adapter,
        _unused_primitive_binding,
        scheduler,
        source,
        action,
        engine,
    ) = _powered_fixture()
    try:
        left, right = engine.initial_state(action, 0), engine.initial_state(action, 1)
        assert engine.interface(action, source.tile, left, right).active
        assert any(
            type(key) is CausalInterfaceKey
            for key in scheduler.results.audit_snapshot().memo
        )
        before = ledger.counters.get("causal_interface_result_early_hits", 0)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm causal interface descended into a child")

        monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
        monkeypatch.setattr(engine, "boundary_chunks", forbidden)
        monkeypatch.setattr(engine, "_append_prefix", forbidden)
        assert engine.interface(action, source.tile, left, right).active
        assert ledger.counters.get("causal_interface_result_early_hits", 0) > before
    finally:
        source.close()


def test_warm_interface_hit_does_not_execute_semantic_observers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        publish_causal_interface(results, key, payload)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm interface hit executed a semantic observer")

        monkeypatch.setattr(type(results.action_authority), "observe", forbidden)
        assert lookup_causal_interface(results, key) == payload
    finally:
        source.close()


def test_primitive_interface_rejects_rebound_action_authority_before_callbacks() -> (
    None
):
    _ledger, _tiles, results, source, key, _payload = causal_interface_binding()
    admitted_authority = results.action_authority

    class SpoofAuthority:
        calls = 0

        def action_record(self, *_args: object, **_kwargs: object) -> Never:
            self.calls += 1
            raise AssertionError("spoofed action-record callback ran")

        def action_children(self, *_args: object, **_kwargs: object) -> Never:
            self.calls += 1
            raise AssertionError("spoofed action-children callback ran")

        def observe(self, *_args: object, **_kwargs: object) -> Never:
            self.calls += 1
            raise AssertionError("spoofed observer ran")

    spoof = SpoofAuthority()
    object.__setattr__(results, "action_authority", spoof)
    try:
        with pytest.raises(
            ValueError, match="action authority changed after admission"
        ):
            primitive_interface_payload(
                results,
                key.action,
                key.input,
                PrimitiveCausalPorts(*key.ports),
                key.wiring,
                TemporalCocycle(),
            )
        assert spoof.calls == 0
    finally:
        object.__setattr__(results, "action_authority", admitted_authority)
        source.close()


def test_warm_interface_rejects_mutated_publication_record() -> None:
    _ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        publish_causal_interface(results, key, payload)
        record = results.audit_snapshot().memo[key]
        object.__setattr__(record, "active", not payload.active)
        with pytest.raises(ValueError, match="publication metadata was modified"):
            lookup_causal_interface(results, key)
        object.__setattr__(record, "active", payload.active)
    finally:
        source.close()


def test_warm_interface_seal_covers_boundary_orientation() -> None:
    _ledger, tiles, results, source, key, payload = causal_interface_binding()
    view = BoundaryTileView(source.tile, 0, tiles.resolve(source.tile).width)
    bound_key = replace(key, boundaries=BoundaryTileOperands(view, None))
    try:
        publish_causal_interface(results, bound_key, payload)
        record = results.audit_snapshot().memo[bound_key]
        assert isinstance(record, CompletedInterfaceResult)
        object.__setattr__(view, "orientation", 1)
        with pytest.raises(ValueError, match="publication metadata was modified"):
            validate_published_causal_interface_value(results, bound_key, record)
        object.__setattr__(view, "orientation", 0)
    finally:
        source.close()


def test_publication_snapshot_covers_producer_and_consumer_orientations() -> None:
    _ledger, tiles, results, source, key, payload = causal_interface_binding()
    try:
        width = tiles.resolve(source.tile).width
        forward = BoundaryTileOperands(BoundaryTileView(source.tile, 0, width), None)
        mirrored = BoundaryTileOperands(
            BoundaryTileView(source.tile, 0, width, 1), None
        )
        producer = BoundPorts(key.ports, key.wiring, forward)
        consumer = BoundPorts(key.ports, key.wiring, forward)
        base = replace(key, fusion=FusedBoundaryContract(producer, consumer))
        record = results.audit_snapshot().memo.get(key)
        if record is None:
            publish_causal_interface(results, key, payload)
            record = results.audit_snapshot().memo[key]
        assert isinstance(record, CompletedInterfaceResult)
        producer_changed = replace(
            base,
            fusion=FusedBoundaryContract(
                BoundPorts(key.ports, key.wiring, mirrored),
                consumer,
            ),
        )
        consumer_changed = replace(
            base,
            fusion=FusedBoundaryContract(
                producer,
                BoundPorts(key.ports, key.wiring, mirrored),
            ),
        )
        assert causal_interface_snapshot(base, record) != causal_interface_snapshot(
            producer_changed,
            record,
        )
        assert causal_interface_snapshot(base, record) != causal_interface_snapshot(
            consumer_changed,
            record,
        )
    finally:
        source.close()


def test_causal_interface_fused_consumer_wiring_matches_top_level_context() -> None:
    from tests.support.tile_results import setup_tile_results

    (
        ledger,
        _actions,
        _tiles,
        results,
        input_lease,
        output_lease,
        result_key,
        _result,
    ) = setup_tile_results()
    base = causal_interface_key(result_key)
    matching = BoundPorts(base.ports, base.wiring, base.boundaries)
    valid = replace(base, fusion=FusedBoundaryContract(matching, matching))
    assert lookup_causal_interface(results, valid) is None

    alternate = ResultWiring(
        base.wiring.signature,
        1 - base.wiring.orientation,
        base.wiring.phase,
    )
    mismatched = replace(
        base,
        fusion=FusedBoundaryContract(
            BoundPorts(base.ports, alternate, base.boundaries),
            BoundPorts(base.ports, alternate, base.boundaries),
        ),
    )
    before = ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="consumer edge"):
            lookup_causal_interface(results, mismatched)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert after.counters.get("causal_interface_result_requests", 0) == (
            before.counters.get("causal_interface_result_requests", 0)
        )
        assert mismatched not in results.audit_snapshot().memo
    finally:
        input_lease.close()
        output_lease.close()


def test_causal_interface_binding_retires_with_its_exact_input() -> None:
    _ledger, _tiles, results, source, key, payload = causal_interface_binding()
    publish_causal_interface(results, key, payload)
    assert key in results.audit_snapshot().memo
    source.close()
    assert key not in results.audit_snapshot().memo
    assert not results.audit_snapshot().reverse


def test_causal_interface_binding_has_independent_read_only_inventory() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        publish_causal_interface(results, key, payload)
        before = ledger.snapshot()
        metrics = collect_ledger_metrics(ledger)
        assert ledger.snapshot() == before
        assert metrics.resource_audit_complete == 1
        assert metrics.resource_accounting_mismatch == 0
        assert metrics.tile_execution_memo_entries == results.retained_entries
        assert (
            sum(
                type(item) is CausalInterfaceKey
                for item in results.audit_snapshot().memo
            )
            == 1
        )
        assert metrics.completed_result_entries == 0
    finally:
        source.close()


def test_causal_interface_publication_is_atomic_at_exhausted_budget() -> None:
    ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        ledger.max_cache_entries = ledger.entries
        memo_before = dict(results.audit_snapshot().memo)
        reverse_before = dict(results.audit_snapshot().reverse)
        accounting = (ledger.entries, ledger.nodes)
        with pytest.raises(BlockContextBudgetExceeded):
            publish_causal_interface(results, key, payload)
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


def test_causal_interface_rejects_forged_derived_behavior_before_mutation() -> None:
    ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        malformed = replace(
            payload,
            outgoing_ports=(1 - payload.outgoing_ports[0], payload.outgoing_ports[1]),
        )
        before = ledger.snapshot()
        with pytest.raises(ValueError):
            publish_causal_interface(results, key, malformed)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
    finally:
        source.close()


def test_causal_interface_port_aliases_reject_before_warm_lookup() -> None:
    ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        publish_causal_interface(results, key, payload)
        for bad in (False, True, 0.0, 1.0):
            malformed = replace(key, ports=(cast(int, bad), key.ports[1]))
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                lookup_causal_interface(results, malformed)
            after = ledger.snapshot()
            assert (after.entries, after.nodes, after.counters) == (
                before.entries,
                before.nodes,
                before.counters,
            )
    finally:
        source.close()


def test_causal_interface_foreign_tile_rejects_before_lookup() -> None:
    ledger, _tiles, results, source, key, payload = causal_interface_binding()
    try:
        publish_causal_interface(results, key, payload)
        foreign = TileID(ArenaToken("foreign"), key.input.kind, key.input.local_id)
        malformed = CausalInterfaceKey(
            key.action,
            foreign,
            key.ports,
            key.wiring,
            key.boundaries,
            key.fusion,
        )
        before = ledger.snapshot()
        with pytest.raises(ValueError):
            lookup_causal_interface(results, malformed)
        after = ledger.snapshot()
        assert (after.entries, after.nodes, after.counters) == (
            before.entries,
            before.nodes,
            before.counters,
        )
    finally:
        source.close()


def test_live_and_closed_causal_spatial_buffers_have_complete_inventory() -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    (
        ledger,
        _unused_tiles_binding,
        _adapter,
        _unused_action_binding,
        scheduler,
        source,
    ) = make_tile_runtime_source(BaseBlockEffect(3), (0, 1))
    buffer = scheduler.causal_workspace.allocate(2)
    try:
        buffer.append(source.tile)
        assert not audit_field_image_payloads(ledger).invalid
        assert collect_ledger_metrics(ledger).resource_audit_complete == 1
    finally:
        buffer.close()
        source.close()
    assert not audit_field_image_payloads(ledger).invalid
    assert collect_ledger_metrics(ledger).resource_audit_complete == 1


def test_causal_spatial_buffer_forged_metadata_is_reported() -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    ledger, _tiles, _adapter, _action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    buffer = scheduler.causal_workspace.allocate(1)
    try:
        buffer.used = 2
        assert audit_field_image_payloads(ledger).invalid
        buffer.used = 0
    finally:
        buffer.close()


def test_failed_causal_interface_releases_all_transient_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    (
        ledger,
        _unused_tiles_binding,
        adapter,
        _unused_primitive_binding,
        scheduler,
        source,
        action,
        engine,
    ) = _powered_fixture()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise RuntimeError("injected causal interface failure")

    monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
    try:
        with pytest.raises(RuntimeError, match="injected causal interface failure"):
            engine.interface(
                action,
                source.tile,
                engine.initial_state(action, 0),
                engine.initial_state(action, 1),
            )
        assert not scheduler.causal_workspace.audit_snapshot().buffers
        assert not scheduler.causal_workspace.audit_snapshot().references
        task_state = scheduler.causal_tasks.audit_snapshot()
        assert not task_state.memo_items
        assert not task_state.active_items
        metrics = collect_ledger_metrics(ledger)
        assert metrics.resource_accounting_mismatch == 0
        assert metrics.resource_audit_complete == 1
    finally:
        source.close()


def test_suspended_causal_frame_stack_has_complete_live_inventory(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    (
        ledger,
        _unused_tiles_binding,
        adapter,
        _unused_primitive_binding,
        scheduler,
        source,
        action,
        engine,
    ) = _powered_fixture()
    original = adapter.leaf_interface_symbol
    observed: list[int] = []

    def inspect(
        action: FieldCellActionID,
        symbol: int,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> tuple[int, LocalInterfaceID, TemporalCocycle]:
        if not observed:
            audit = audit_field_image_payloads(ledger)
            assert not audit.invalid
            observed.append(len(scheduler.causal_tasks.audit_snapshot().frames.values))
        return original(action, symbol, ports, wiring)

    monkeypatch.setattr(adapter, "leaf_interface_symbol", inspect)
    try:
        engine.interface(
            action,
            source.tile,
            engine.initial_state(action, 0),
            engine.initial_state(action, 1),
        )
        assert observed and max(observed) > 0
        assert not scheduler.causal_tasks.audit_snapshot().frames.values
    finally:
        source.close()


def test_forged_causal_frame_metadata_is_reported() -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    ledger, _tiles, _adapter, _action, scheduler, source = make_tile_runtime_source(
        BaseBlockEffect(3), (0,)
    )
    scheduler.causal_tasks.frames.append(
        ExactReverseOutputFrame((source.tile,), stage=-2)
    )
    try:
        assert audit_field_image_payloads(ledger).invalid
    finally:
        scheduler.causal_tasks.frames.clear()
        source.close()


def _powered_fixture() -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
    TileLease,
    FieldCellActionID,
    CausalTileEngine,
]:
    values = make_tile_runtime_source(BaseBlockEffect(3), (0, 0, 0, 1))
    _, _, adapter, primitive, scheduler, _ = values
    return (*values, adapter.power(primitive, 4), CausalTileEngine(scheduler))
