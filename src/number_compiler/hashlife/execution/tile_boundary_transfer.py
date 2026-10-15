"""Directed scans of canonical spatial operands, using the shared interface memo.

A view selects an exact source interval.  Transfer visits maximal covered
parents; it never emits their output or constructs a copied prefix tape.
"""

from __future__ import annotations

from typing import Protocol

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import BoundPorts, ResultWiring
from number_compiler.hashlife.tiles.tile_result_validation import (
    validate_boundary_operands,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


class _Host(Protocol):
    tiles: TileArena
    ledger: ResourceLedger

    def _require_results(self) -> CompletedResultArena: ...

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...
    def primitive_law(self, action: FieldCellActionID) -> PrimitiveKernel: ...
    def validate_input(self, action: FieldCellActionID, source: TileID) -> None: ...
    def validate_wiring(
        self, action: FieldCellActionID, wiring: ResultWiring
    ) -> None: ...
    def _compile_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID: ...
    def _observe(
        self,
        interface: LocalInterfaceID,
        channel: str,
        ports: tuple[int, ...],
    ) -> int: ...


def validate_boundaries(
    host: _Host,
    action: FieldCellActionID,
    boundaries: BoundaryTileOperands,
    wiring: ResultWiring,
) -> None:
    """Validate exact spatial operands for finite or causal transfer tasks."""
    host.validate_wiring(action, wiring)
    validate_boundary_operands(host.tiles, boundaries)
    for tile in boundaries.tile_ids():
        host.validate_input(action, tile)


def transfer_view(
    host: _Host,
    action: FieldCellActionID,
    view: BoundaryTileView,
    context: BoundPorts,
    side: int,
) -> int:
    """Return one directed exit over a clipped view using maximal tile effects."""
    if type(side) is not int or side not in (0, 1):
        raise ValueError("boundary transfer side requires zero or one")
    if type(context) is not BoundPorts or type(view) is not BoundaryTileView:
        raise TypeError("boundary transfer requires a typed view and ports")
    context.__post_init__()
    if context.boundaries != BoundaryTileOperands():
        raise ValueError(
            "a directed view transfer requires already bound incoming ports"
        )
    validate_boundaries(host, action, BoundaryTileOperands(view), context.wiring)
    host._require_results().validate_shape(action, context.ports, context.wiring)
    if len(context.ports) != 2:
        raise ValueError("primitive boundary transfer requires two finite ports")
    host.ledger.bump(_execution_keys.TILE_BOUNDARY_TRANSFER_REQUESTS)
    children = host.action_children(action)
    width = host.tiles.resolve(view.tile).width
    mirror = host.tiles.mirror(view.tile) if view.orientation else None
    try:
        tile = view.tile if mirror is None else mirror.tile
        start = view.source_offset
        if view.orientation:
            start = width - start - view.relative_extent
        stop = start + view.relative_extent
        pending = [(tile, 0)]
        state = context.ports[side]
        while pending:
            current, origin = pending.pop()
            host.ledger.bump(_execution_keys.TILE_BOUNDARY_TRANSFER_FRAMES)
            node = host.tiles.resolve(current)
            end = origin + node.width
            if end <= start or stop <= origin:
                continue
            if start <= origin and end <= stop:
                ports = (context.ports[0], state) if side else (state, context.ports[1])
                if children is None:
                    from number_compiler.hashlife.execution.tile_directed_transfer import (
                        directed_transfer,
                    )

                    state = directed_transfer(
                        host,
                        action,
                        current,
                        side,
                        state,
                        context.wiring,
                    )
                else:
                    interface = host._compile_interface(action, current, context.wiring)
                    state = host._observe(
                        interface,
                        "boundary_right" if side else "boundary_left",
                        ports,
                    )
                host.ledger.bump(
                    _execution_keys.TILE_BOUNDARY_TRANSFER_PARENT_OBSERVATIONS
                )
                continue
            if node.left is None or node.right is None:
                raise ValueError("clipped boundary transfer reached a malformed tile")
            left, right = (node.left, origin), (node.right, origin + node.width // 2)
            pending.extend((left, right) if side else (right, left))
            host.ledger.bump(_execution_keys.TILE_BOUNDARY_TRANSFER_DESCENTS)
            previous = host.ledger.counters.get(
                _execution_keys.TILE_BOUNDARY_TRANSFER_WORKSPACE_PEAK, 0
            )
            if len(pending) > previous:
                host.ledger.bump(
                    _execution_keys.TILE_BOUNDARY_TRANSFER_WORKSPACE_PEAK,
                    len(pending) - previous,
                )
        return state
    finally:
        if mirror is not None:
            mirror.close()


def bind_boundaries(
    host: _Host,
    action: FieldCellActionID,
    context: BoundPorts,
) -> BoundPorts:
    """Consume independent exact exteriors into this primitive's finite ports."""
    if type(context) is not BoundPorts:
        raise TypeError("boundary binding requires typed finite ports")
    context.__post_init__()
    validate_boundaries(host, action, context.boundaries, context.wiring)
    host._require_results().validate_shape(action, context.ports, context.wiring)
    left, right = context.boundaries.left, context.boundaries.right
    incoming = BoundPorts(context.ports, context.wiring)
    left_exit = (
        context.ports[0]
        if left is None
        else transfer_view(host, action, left, incoming, 0)
    )
    right_exit = (
        context.ports[1]
        if right is None
        else transfer_view(host, action, right, incoming, 1)
    )
    return BoundPorts((left_exit, right_exit), context.wiring)


__all__ = ["bind_boundaries", "transfer_view", "validate_boundaries"]
