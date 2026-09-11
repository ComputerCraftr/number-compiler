"""Evaluate bounded clock leaves without re-entering temporal dispatch."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import TileID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def complete_clock_kernel(
    scheduler: TileScheduler, action: FieldCellActionID, source: TileID
) -> ResultLease:
    """Run a one-to-three tick kernel through the existing iterative engines."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("a clock leaf requires a primitive tile kernel adapter")
    ticks = adapter.action_cocycle(action).physical_ticks
    if not 1 <= ticks <= 3:
        raise ValueError("a clock leaf must have one to three physical ticks")
    key = PoweredResultKey(
        action, source, adapter.initial_ports(action), adapter.wiring(action)
    )
    found = scheduler._lookup_execution_key(key)
    if found is not None:
        scheduler.ledger.bump("tile_scheduler_parent_early_hits")
        return found
    from number_compiler.hashlife.execution.tile_causal_entry import causal_complete

    scheduler.ledger.bump("tile_clock_kernel_evaluations")
    result = causal_complete(scheduler, key)
    if result is not None:
        return result
    scheduler.ledger.bump("tile_scheduler_direct_requests")
    return scheduler._complete_direct(key, checked_miss=True)
