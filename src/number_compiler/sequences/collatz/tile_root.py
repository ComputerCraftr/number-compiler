"""Skip an initial odd Collatz event using canonical source-root summaries."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.source_root_match_memo import source_root_match
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.resources.metric_keys import collatz as _collatz_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def initial_event_shift(
    scheduler: TileScheduler, key: PoweredResultKey
) -> tuple[FieldCellActionID, int] | None:
    """Return C and a geometric shift only inside the first proven odd event.

    Matching the low bits of -1/3 determines v2(3*x+1).  This proof does not
    extend across the next odd event and never constructs that future value.
    """
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    scheduler.results.validate_key(key)
    action = adapter._action(key.action)
    ticks = action.cocycle.physical_ticks
    if (
        not action.homogeneous
        or type(adapter.kernels.kernel(action.kernel).effect)
        is not CollatzPhysicalBlockEffect
        or action.cocycle != TemporalCocycle(ticks)
        or ticks < 3
        or key.fusion is not None
        or key.region is not None
        or key.boundaries.tile_ids()
        or key.ports != adapter.initial_ports(key.action)
        or key.wiring != adapter.wiring(key.action)
    ):
        return None
    scheduler.ledger.bump(_collatz_keys.COLLATZ_INITIAL_ROOT_REQUESTS)
    root = scheduler.tiles.resolve(key.input)
    if root.last_active is None or root.last_active + 3 > root.width:
        # The finite-word primitive must have room for its complete carry.
        # Otherwise shifting its clipped output is not the integer law.
        scheduler.ledger.bump(_collatz_keys.COLLATZ_INITIAL_ROOT_DECLINES)
        return None
    summary = source_root_match(scheduler.results, key.input)
    valuation = summary.phase0_first_mismatch
    if valuation is None:
        raise AssertionError("padded Collatz root has no mismatch before its edge")
    if valuation == 0 or ticks > valuation + 1:
        scheduler.ledger.bump(_collatz_keys.COLLATZ_INITIAL_ROOT_DECLINES)
        return None
    primitive = adapter._action_keys.get(
        ("power", action.kernel, 1, TemporalCocycle(1))
    )
    if type(primitive) is not int:
        raise ValueError("Collatz power has no canonical primitive action")
    return adapter._handle(primitive), ticks - 1
