"""Transient causal storage is owned, budgeted, and released on every path."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.causal_workspace import (
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership
from tests.support.assertions import assert_rejected_atomically


def test_spatial_buffers_charge_full_capacity_and_share_one_inventory() -> None:
    ledger = ResourceLedger()
    workspace = CausalSpatialWorkspace(ledger, "test")
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
        assert audit_execution_ownership(ledger).violations == ()
        assert all(row.accounting_delta == 0 for row in ledger.inventory())
        buffer.close()
        with pytest.raises(ValueError, match="closed"):
            buffer.append(3)
        assert ledger.entries == ledger.nodes == workspace.slots == 0
    assert len(ledger.inventory()) == owners
    assert ledger.counters["tile_causal_spatial_buffer_allocations"] == 20
    assert ledger.counters["tile_causal_spatial_buffer_peak_slots"] == 8


def test_zero_workspace_budget_rejects_before_buffer_constructor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.causal_workspace import SpatialReferenceBuffer

    ledger = ResourceLedger(max_cache_entries=0)
    workspace = CausalSpatialWorkspace(ledger, "test")

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
    workspace = CausalTaskWorkspace(ledger, "test")
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
    workspace = CausalTaskWorkspace(ledger, "test")
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
    workspace = CausalTaskWorkspace(ledger, "result-test")
    ledger.register_execution_root(workspace)
    result = ("bounded-result", 1)
    workspace.values.append(result)
    assert_rejected_atomically(
        ledger,
        lambda: workspace.values.append(("unpublished-result", 2)),
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
    from tests.support.tile_kernel import _runtime, _tile

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source:
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
        assert not scheduler._causal_tasks.memo
        assert not scheduler._causal_tasks.active
        assert not scheduler._causal_tasks.frames
        assert not scheduler._causal_workspace
        assert all(row.accounting_delta == 0 for row in ledger.inventory())
