"""Execution-context admission layered after completed-result key validation."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def validate_execution_context(self: TileScheduler, key: PoweredResultKey) -> None:
    """Check adapter laws; the caller must also admit the result-arena key."""
    contexts: tuple[
        tuple[FieldCellActionID, BoundaryTileOperands, ResultWiring], ...
    ] = ((key.action, key.boundaries, key.wiring),)
    if key.fusion is not None:
        children = self._children(key.action)
        if children is None:
            raise ValueError("fused execution requires two temporal children")
        contexts = tuple(
            (child, bound.boundaries, bound.wiring)
            for child, bound in zip(
                children, (key.fusion.producer, key.fusion.consumer), strict=True
            )
        )
    for action, boundaries, wiring in contexts:
        if boundaries == BoundaryTileOperands():
            continue
        validator = getattr(self.adapter, "validate_boundaries", None)
        if validator is None:
            from number_compiler.hashlife.actions.lazy_compiler import (
                UnsupportedInterfaceError,
            )

            raise UnsupportedInterfaceError(
                "adapter has no boundary-tile execution law"
            )
        validator(action, boundaries, wiring)
    input_validator = getattr(self.adapter, "validate_input", None)
    if input_validator is not None:
        input_validator(key.action, key.input)
    validator = getattr(self.adapter, "validate_wiring", None)
    if validator is not None:
        validator(key.action, key.wiring)
