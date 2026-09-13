"""Ordered physical-Collatz support carried by completed tile results."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.sequences.collatz.physical_support import PhysicalSupport

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tiles import TileID


def primitive_physical_support(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
) -> PhysicalSupport | None:
    """Return the unique low-boundary branch atom for a primitive scan."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.sequences.collatz.block_power import (
        CollatzPhysicalBlockEffect,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    record = adapter._action(action)
    if record.children is not None:
        return None
    kernel = adapter.kernels.kernel(record.kernel)
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        return None
    if len(ports) != 2:
        raise ValueError("physical support requires two admitted boundary ports")
    symbol = scheduler.tiles.resolve(source).symbol
    if ports[0] != kernel.initial(BoundarySide.LEFT) or symbol not in (0, 1):
        return scheduler.physical_supports.identity
    return (
        scheduler.physical_supports.odd if symbol else scheduler.physical_supports.even
    )


def spatial_physical_support(
    left: PhysicalSupport | None,
    right: PhysicalSupport | None,
) -> PhysicalSupport | None:
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
    before: PhysicalSupport | None,
    after: PhysicalSupport | None,
    *,
    before_ticks: int,
    after_ticks: int,
) -> PhysicalSupport | None:
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
