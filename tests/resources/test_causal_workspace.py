"""Transient causal storage is owned, budgeted, and released on every path."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.causal_types import CausalPrefix, CausalSpatialValue
from number_compiler.resources.causal_workspace import (
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.ownership import audit_execution_ownership
from tests.support.assertions import assert_rejected_atomically


def test_spatial_buffers_charge_full_capacity_and_share_one_inventory() -> None:
    ledger = ResourceLedger()
    workspace: CausalSpatialWorkspace[CausalSpatialValue] = CausalSpatialWorkspace(
        ledger, "test"
    )
    ledger.register_execution_root(workspace)
    owners = len(ledger.inventory())
    for _ in range(20):
        buffer = workspace.allocate(8)
        buffer.append(1)
        buffer.append(2)
        buffer.reverse()
        assert tuple(buffer) == (2, 1)
        assert ledger.entries == 9
        assert ledger.nodes == 1
        assert workspace.slots == 8
        assert buffer.capacity == 8
        assert buffer.used == 2
        references = workspace.audit_snapshot().references
        assert len(references) == buffer.capacity
        assert dict(references) == {
            (buffer.identity, index): value
            for index, value in enumerate((2, 1, None, None, None, None, None, None))
        }
        assert audit_execution_ownership(ledger).violations == ()
        assert all(row.accounting_delta == 0 for row in ledger.inventory())
        buffer.close()
        assert not workspace.audit_snapshot().references
        with pytest.raises(ValueError, match="closed"):
            buffer.append(3)
        assert ledger.entries == ledger.nodes == workspace.slots == 0
    assert len(ledger.inventory()) == owners
    assert ledger.counters["tile_causal_spatial_buffer_allocations"] == 20
    assert ledger.counters["tile_causal_spatial_buffer_peak_slots"] == 8


def test_spatial_allocation_accounts_for_native_reference_table_growth() -> None:
    ledger = ResourceLedger()
    workspace: CausalSpatialWorkspace[CausalSpatialValue] = CausalSpatialWorkspace(
        ledger, "test"
    )
    allocated_key = _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_ALLOCATED_BYTES
    peak_bytes_key = _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_PEAK_BYTES
    initial = workspace.audit_snapshot()
    old_ref_bytes = initial.reference_store.backing_bytes
    old_buffer_bytes = initial.buffer_store.backing_bytes
    old_allocated = ledger.counters.get(allocated_key, 0)
    buffer = workspace.allocate(128)
    allocated = workspace.audit_snapshot()
    ref_growth = allocated.reference_store.backing_bytes - old_ref_bytes
    buffer_growth = allocated.buffer_store.backing_bytes - old_buffer_bytes
    assert ref_growth > 0
    assert ledger.counters.get(allocated_key, 0) == (
        old_allocated + buffer.backing_bytes + ref_growth + buffer_growth
    )
    allocated_after_allocation = ledger.counters.get(allocated_key, 0)
    peak_after_allocation = ledger.counters.get(peak_bytes_key, 0)
    assert peak_after_allocation == workspace.backing_bytes
    try:
        for value in range(buffer.capacity):
            buffer.append(value)
            assert ledger.counters.get(allocated_key, 0) == allocated_after_allocation
            assert ledger.counters.get(peak_bytes_key, 0) == peak_after_allocation
    finally:
        buffer.close()


def test_spatial_append_rolls_back_both_failed_store_hooks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace: CausalSpatialWorkspace[CausalSpatialValue] = CausalSpatialWorkspace(
        ledger, "test"
    )
    retained = workspace.allocate(2)
    attempted = workspace.allocate(2)
    retained.append(1)
    calls = 0

    def fail_invalidation() -> None:
        nonlocal calls
        calls += 1
        raise RuntimeError("spatial reference invalidation failed")

    try:
        with monkeypatch.context() as patch:
            patch.setattr(ledger, "note_store_mutation", fail_invalidation)
            with pytest.raises(
                RuntimeError, match="spatial reference invalidation failed"
            ):
                attempted.append(2)

        assert calls == 2
        assert tuple(retained) == (1,)
        assert tuple(attempted) == ()
        assert retained.used == 1
        assert attempted.used == 0
        references = workspace.audit_snapshot().references
        assert len(references) == 4
        assert dict(references) == {
            (retained.identity, 0): 1,
            (retained.identity, 1): None,
            (attempted.identity, 0): None,
            (attempted.identity, 1): None,
        }
        assert ledger.entries == 6
        assert workspace.slots == 4
        assert (
            ledger.counters[_resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_APPEND_FAILURES]
            == 1
        )
        assert ledger.counters[_resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_APPENDS] == 1
    finally:
        attempted.close()
        retained.close()


def test_task_stack_append_failures_release_their_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution.causal_frames import MemoDoneFrame

    ledger = ResourceLedger()
    workspace = CausalTaskWorkspace(ledger, "test")
    frame = MemoDoneFrame((("memo", ()),))
    calls = 0

    def fail_invalidation() -> None:
        nonlocal calls
        calls += 1
        raise RuntimeError("task stack invalidation failed")

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "note_store_mutation", fail_invalidation)
        with pytest.raises(RuntimeError, match="task stack invalidation failed"):
            workspace.frames.append(frame)
        with pytest.raises(RuntimeError, match="task stack invalidation failed"):
            workspace.values.append(True)

    assert calls == 4
    assert len(workspace.frames) == len(workspace.values) == 0
    assert workspace.frames.payload_references == 0
    assert ledger.entries == ledger.nodes == 0
    workspace.clear()


def test_causal_and_reverse_summary_frames_have_distinct_audited_stacks() -> None:
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.execution.causal_frames import SourceRootMatchFrame
    from number_compiler.hashlife.tiles.reverse_threshold_summary import (
        ReverseThresholdFrame,
    )
    from number_compiler.resources.tile_runtime_inventory import audit_tile_runtime
    from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime

    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with make_tile_from_symbols(tiles, adapter, primitive, (0, 1)) as source:
        owners = scheduler.audit_causal_owners()
        tasks = owners.tasks
        prefix = CausalPrefix(primitive, 0, 0, 0)
        prefix_key = ("advance", (prefix,))
        tasks.begin(prefix_key)
        tasks.finish(prefix_key, prefix)
        spatial_buffer = owners.spatial.allocate(4)
        spatial_buffer.append(source.tile)
        task_frame = SourceRootMatchFrame((source.tile,))
        summary_frame = ReverseThresholdFrame((source.tile,))
        tasks.frames.append(task_frame)
        tasks.summary_frames.append(summary_frame)
        spatial_used = spatial_buffer.used

        assert tasks.frames.owner != tasks.summary_frames.owner
        task_storage: object = tasks.audit_snapshot().frames.store
        summary_storage: object = tasks.audit_snapshot().summary_frames.store
        assert task_storage is not summary_storage
        assert tasks.frames.payload_references == 1
        assert tasks.summary_frames.payload_references == 1

        def runtime_invalid() -> set[tuple[int, int]]:
            _, invalid = audit_tile_runtime(
                ledger,
                dict(ledger.iter_containers()),
                tuple(ledger.iter_execution_roots()),
            )
            return invalid

        try:
            assert not runtime_invalid()

            spatial_buffer.used = 10**9
            assert (
                owners.spatial.audit_snapshot().buffer_owner,
                id(spatial_buffer),
            ) in runtime_invalid()
            spatial_buffer.used = 1

            tasks.frames.payload_references -= 1
            assert (tasks.frames.owner, id(tasks.frames)) in runtime_invalid()
            tasks.frames.payload_references += 1

            tasks.summary_frames.payload_references -= 1
            assert (
                tasks.summary_frames.owner,
                id(tasks.summary_frames),
            ) in runtime_invalid()
            tasks.summary_frames.payload_references += 1
        finally:
            spatial_buffer.used = spatial_used
            tasks.clear()
            spatial_buffer.close()


def test_zero_workspace_budget_rejects_before_buffer_constructor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.causal_workspace import SpatialReferenceBuffer

    ledger = ResourceLedger(max_cache_entries=0)
    workspace: CausalSpatialWorkspace[CausalSpatialValue] = CausalSpatialWorkspace(
        ledger, "test"
    )

    def forbidden(*_args: object) -> Never:
        raise AssertionError("allocated before budget reservation")

    monkeypatch.setattr(SpatialReferenceBuffer, "__init__", forbidden)
    assert_rejected_atomically(
        ledger, lambda: workspace.allocate(1), BlockContextBudgetExceeded
    )


def test_task_memo_failed_completion_preserves_active_dependency_until_cleanup() -> (
    None
):
    ledger = ResourceLedger(max_cache_entries=1)
    workspace: CausalTaskWorkspace = CausalTaskWorkspace(ledger, "test")
    key = ("transfer", (1, 2))
    workspace.begin(key)
    assert_rejected_atomically(
        ledger, lambda: workspace.finish(key, 3), BlockContextBudgetExceeded
    )
    assert key in workspace.active
    assert not workspace.memo
    workspace.clear()
    assert ledger.entries == 0
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_task_workspace_reuses_registration_and_rejects_cycles() -> None:
    ledger = ResourceLedger()
    workspace: CausalTaskWorkspace = CausalTaskWorkspace(ledger, "test")
    ledger.register_execution_root(workspace)
    key = ("transfer", (1, 2))
    workspace.begin(key)
    assert_rejected_atomically(
        ledger, lambda: workspace.begin(key), ValueError, match="cycle"
    )
    workspace.finish(key, 3)
    assert workspace.memo[key] == 3
    assert ledger.entries == 1
    assert audit_execution_ownership(ledger).violations == ()
    workspace.clear()
    assert ledger.entries == 0


def test_result_workspace_reserves_before_publish_and_releases_on_cleanup() -> None:
    ledger = ResourceLedger(max_cache_entries=1)
    workspace: CausalTaskWorkspace = CausalTaskWorkspace(ledger, "result-test")
    ledger.register_execution_root(workspace)
    result = False
    workspace.values.append(result)
    assert_rejected_atomically(
        ledger,
        lambda: workspace.values.append(True),
        BlockContextBudgetExceeded,
    )
    assert len(workspace.values) == 1
    assert workspace.values.pop() is result
    assert ledger.entries == 0
    workspace.values.append(result)
    workspace.clear()
    assert not workspace.values
    assert ledger.entries == 0
    assert audit_execution_ownership(ledger).violations == ()
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_causal_frame_budget_rejects_before_primitive_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime

    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with make_tile_from_symbols(tiles, adapter, primitive, (0, 0, 0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        before_entries, before_nodes = ledger.entries, ledger.nodes
        ledger.max_cache_entries = before_entries

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("primitive executed with exhausted workspace budget")

        monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
        with pytest.raises(BlockContextBudgetExceeded):
            engine.point(action, source.tile, 0)
        assert ledger.entries == before_entries
        assert ledger.nodes == before_nodes
        owners = scheduler.audit_causal_owners()
        task_snapshot = owners.tasks.audit_snapshot()
        spatial_snapshot = owners.spatial.audit_snapshot()
        assert not task_snapshot.memo_items
        assert not task_snapshot.active_items
        assert not task_snapshot.frames.values
        assert not spatial_snapshot.slots
        assert not spatial_snapshot.buffers
        assert all(row.accounting_delta == 0 for row in ledger.inventory())
