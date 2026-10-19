"""Join family-issued ordered Boolean support on completed tile results.

The shared layer preserves ownership, spatial tick uniqueness and temporal
order. Branch meaning and primitive support construction belong to the
injected family hooks.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.ordered_boolean_support import OrderedBooleanSupport

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tiles import TileID


def primitive_physical_support(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
) -> OrderedBooleanSupport | None:
    """Return the unique low-boundary branch atom for a primitive scan."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    hooks = adapter.family_hooks
    if hooks is None:
        return None
    record = adapter.action_record(action)
    if record.children is not None:
        return None
    if len(ports) != 2:
        raise ValueError("physical support requires two admitted boundary ports")
    return hooks.physical_support(scheduler, action, source, ports)


def spatial_physical_support(
    left: OrderedBooleanSupport | None,
    right: OrderedBooleanSupport | None,
) -> OrderedBooleanSupport | None:
    """Select the one spatial child that owns the low-boundary tick."""
    a, b = left, right
    if a is None and b is None:
        return None
    if a is None or b is None or a.owner is not b.owner:
        raise ValueError("spatial children have incompatible physical support")
    a.owner.validate(a)
    b.owner.validate(b)
    if a.ticks and b.ticks:
        raise ValueError("two spatial children claim one physical tick")
    return a if a.ticks else b


def temporal_physical_support(
    before: OrderedBooleanSupport | None,
    after: OrderedBooleanSupport | None,
    *,
    before_ticks: int,
    after_ticks: int,
) -> OrderedBooleanSupport | None:
    """Concatenate source-rebased supports in chronological order."""
    a, b = before, after
    if a is None and b is None:
        return None
    if a is None:
        if before_ticks:
            raise ValueError("temporal producer omitted its physical support")
        return b
    if b is None:
        if after_ticks:
            raise ValueError("temporal consumer omitted its physical support")
        return a
    if a.owner is not b.owner:
        raise ValueError("temporal children have incompatible physical support")
    return a.owner.concat(a, b)


__all__ = [
    "primitive_physical_support",
    "spatial_physical_support",
    "temporal_physical_support",
]
