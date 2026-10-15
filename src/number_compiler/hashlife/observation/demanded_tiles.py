"""Store-free demanded tiles operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_clock_dispatch import complete_clock
from number_compiler.hashlife.tiles.tile_boundaries import (
    EMPTY_BOUNDARY_TILES,
    BoundaryTileOperands,
)
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    after_context,
    before_context,
)
from number_compiler.hashlife.tiles.tile_ports import (
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_results import (
    PoweredResultKey,
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.metric_keys import (
    hashlife_observation as _observation_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def point(
    self: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
    wiring: ResultWiring,
    coordinate: int,
    *,
    _application: int | None = None,
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
    fusion: FusedBoundaryContract | None = None,
) -> int:
    if type(coordinate) is not int:
        raise TypeError("tile coordinate requires an exact integer")
    root = self.tiles.resolve(source)
    if not 0 <= coordinate < root.width:
        raise IndexError(coordinate)
    action_now, tile_now, ports_now, wiring_now = action, source, ports, wiring
    held: list[ResultLease] = []
    try:
        while True:
            key = self._key(
                action_now, tile_now, ports_now, wiring_now, boundaries, fusion
            )
            found = _probe_demand(
                self, key, len(held), "tile_scheduler_demand_descents"
            )
            if found is not None:
                self.ledger.bump(_shared_keys.TILE_SCHEDULER_DEMAND_PARENT_HITS)
                output = _retain_output(self, key, found, held, _application)
                return self.tiles.point(output, coordinate)
            self.ledger.bump(_observation_keys.TILE_SCHEDULER_DEMAND_PARENT_MISSES)
            clock = complete_clock(self, key, whole_output=False)
            if clock is not None:
                output = _retain_output(self, key, clock, held, _application)
                return self.tiles.point(output, coordinate)
            from number_compiler.hashlife.execution.tile_causal_entry import (
                causal_point,
            )

            causal = causal_point(self, key, coordinate, application=_application)
            if causal is not None:
                return causal
            children, admitted = _probe_midpoint(self, key, held, _application)
            if admitted is not None:
                action_now, tile_now, ports_now, wiring_now, boundaries = admitted
                fusion = None
                continue
            if children is not None:
                from number_compiler.hashlife.execution.tile_fused import (
                    demanded_fused_point,
                )

                fused = demanded_fused_point(self, key, coordinate)
                if fused is not None:
                    return fused
            node = self.tiles.resolve(tile_now)
            if not node.level:
                result = self._complete_leaf(key)
                output = _retain_output(self, key, result, held, _application)
                return self.tiles.point(output, 0)
            if node.left is None or node.right is None:
                raise ValueError("malformed canonical parent")
            half = 1 << (node.level - 1)
            side = int(coordinate >= half)
            context = self._child_context(
                action_now,
                tile_now,
                node.left,
                node.right,
                ports_now,
                wiring_now,
                side,
                boundaries,
            )
            tile_now = node.right if side else node.left
            if side:
                coordinate -= half
            ports_now, wiring_now = context.ports, context.wiring
            boundaries, fusion = context.boundaries, None
    finally:
        for lease in held:
            lease.close()


def width(
    self: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
    wiring: ResultWiring,
    *,
    limit: int | None = None,
    _application: int | None = None,
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
    fusion: FusedBoundaryContract | None = None,
) -> int:
    root = self.tiles.resolve(source)
    stop = root.width if limit is None else limit
    if type(stop) is not int:
        raise TypeError("tile width limit requires an exact integer")
    if not 0 <= stop <= root.width:
        raise ValueError("tile width limit lies outside the source")
    if not stop:
        self._validate_execution_key(
            self._key(action, source, ports, wiring, boundaries, fusion)
        )
        return 0
    action_now, tile_now, ports_now, wiring_now = action, source, ports, wiring
    offset = 0
    remaining = stop
    held: list[ResultLease] = []
    initial_request = True
    try:
        while True:
            key = self._key(
                action_now, tile_now, ports_now, wiring_now, boundaries, fusion
            )
            found = _probe_demand(self, key, len(held), "tile_scheduler_width_descents")
            if found is not None:
                self.ledger.bump(_shared_keys.TILE_SCHEDULER_DEMAND_PARENT_HITS)
                output = _retain_output(self, key, found, held, _application)
                return offset + self.tiles.active_width(output, remaining)
            self.ledger.bump(_observation_keys.TILE_SCHEDULER_DEMAND_PARENT_MISSES)
            if initial_request and fusion is None:
                growth_hook = getattr(self.adapter, "current_growth", None)
                growth = (
                    growth_hook(
                        action_now,
                        tile_now,
                        ports_now,
                        wiring_now,
                        boundaries,
                    )
                    if callable(growth_hook)
                    else None
                )
                if growth is not None:
                    if type(growth) is not int or growth not in (0, 1):
                        raise TypeError("current growth observer returned another sort")
                    self.ledger.bump(
                        _observation_keys.REVERSE_CURRENT_GROWTH_WIDTH_SHORTCUTS
                    )
                    return min(remaining, root.extent + growth)
            initial_request = False
            clock = complete_clock(self, key, whole_output=False)
            if clock is not None:
                output = _retain_output(self, key, clock, held, _application)
                return offset + self.tiles.active_width(output, remaining)
            from number_compiler.hashlife.execution.tile_causal_entry import (
                causal_width_query,
            )

            causal = causal_width_query(self, key, remaining, application=_application)
            if causal is not None:
                return offset + causal
            children, admitted = _probe_midpoint(self, key, held, _application)
            if admitted is not None:
                action_now, tile_now, ports_now, wiring_now, boundaries = admitted
                fusion = None
                continue
            if children is not None:
                from number_compiler.hashlife.execution.tile_fused import (
                    demanded_fused_width,
                )

                fused = demanded_fused_width(self, key, remaining)
                if fused is not None:
                    return offset + fused
            node = self.tiles.resolve(tile_now)
            if not node.level:
                result = self._complete_leaf(key)
                output = _retain_output(self, key, result, held, _application)
                return offset + self.tiles.resolve(output).extent
            if node.left is None or node.right is None:
                raise ValueError("malformed canonical parent")
            half = 1 << (node.level - 1)
            if remaining <= half:
                context = self._child_context(
                    action_now,
                    tile_now,
                    node.left,
                    node.right,
                    ports_now,
                    wiring_now,
                    0,
                    boundaries,
                )
                tile_now = node.left
                ports_now, wiring_now = context.ports, context.wiring
                boundaries, fusion = context.boundaries, None
                continue
            left_context = self._child_context(
                action_now,
                tile_now,
                node.left,
                node.right,
                ports_now,
                wiring_now,
                0,
                boundaries,
            )
            right_context = self._child_context(
                action_now,
                tile_now,
                node.left,
                node.right,
                ports_now,
                wiring_now,
                1,
                boundaries,
            )
            right_limit = remaining - half
            if self._prefix_active(
                action_now,
                node.right,
                right_context.ports,
                right_context.wiring,
                right_limit,
                right_context.boundaries,
            ):
                offset += 1 << (node.level - 1)
                tile_now = node.right
                remaining = right_limit
                ports_now, wiring_now = right_context.ports, right_context.wiring
                boundaries, fusion = right_context.boundaries, None
                continue
            if not self._active_context(action_now, node.left, left_context):
                return 0
            tile_now = node.left
            remaining = half
            ports_now, wiring_now = left_context.ports, left_context.wiring
            boundaries, fusion = left_context.boundaries, None
    finally:
        for lease in held:
            lease.close()


def _prefix_active(
    self: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
    wiring: ResultWiring,
    limit: int,
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
) -> bool:
    """Observe covered parent effects with one iterative clipped-range loop."""
    if not 0 <= limit <= self.tiles.resolve(source).width:
        raise ValueError("activity prefix lies outside its source")
    pending = [(source, ChildContext(ports, wiring, boundaries), limit)]
    while pending:
        self._workspace_peak(len(pending))
        tile, context, remaining = pending.pop()
        if not remaining:
            continue
        node = self.tiles.resolve(tile)
        if remaining == node.width or not node.level:
            if self._active_context(action, tile, context):
                return True
            continue
        if node.left is None or node.right is None:
            raise ValueError("malformed canonical parent")
        half = node.width // 2
        left = self._child_context(
            action,
            tile,
            node.left,
            node.right,
            context.ports,
            context.wiring,
            0,
            context.boundaries,
        )
        pending.append((node.left, left, min(half, remaining)))
        if remaining > half:
            right = self._child_context(
                action,
                tile,
                node.left,
                node.right,
                context.ports,
                context.wiring,
                1,
                context.boundaries,
            )
            pending.append((node.right, right, remaining - half))
    return False


def _retain_output(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    result: ResultLease,
    held: list[ResultLease],
    application: int | None,
) -> TileID:
    """Keep the result alive for the observation or its application owner."""
    output = result.output
    if application is None:
        held.append(result)
    else:
        scheduler._pin(application, key, result)
    return output


def _admitted_midpoint(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    children: tuple[FieldCellActionID, FieldCellActionID],
    held: list[ResultLease],
    application: int | None,
) -> (
    tuple[
        FieldCellActionID, TileID, tuple[int, ...], ResultWiring, BoundaryTileOperands
    ]
    | None
):
    """Transport the consumer only when the producer image is already admitted."""
    producer = before_context(scheduler, key, children[0])
    before_key = scheduler._key(
        children[0], key.input, producer.ports, producer.wiring, producer.boundaries
    )
    midpoint = scheduler._lookup_execution_key(before_key)
    if midpoint is None:
        return None
    scheduler.ledger.bump(_shared_keys.TILE_SCHEDULER_MIDPOINT_HITS)
    context = after_context(scheduler, key, children[1], midpoint.result)
    return (
        children[1],
        _retain_output(scheduler, before_key, midpoint, held, application),
        context.ports,
        context.wiring,
        context.boundaries,
    )


def _probe_demand(
    scheduler: TileScheduler, key: PoweredResultKey, held_count: int, counter: str
) -> ResultLease | None:
    result = scheduler._lookup_execution_key(key)
    scheduler._workspace_peak(held_count + 1)
    scheduler.ledger.bump(counter)
    return result


def _probe_midpoint(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    held: list[ResultLease],
    application: int | None,
) -> tuple[
    tuple[FieldCellActionID, FieldCellActionID] | None,
    tuple[
        FieldCellActionID, TileID, tuple[int, ...], ResultWiring, BoundaryTileOperands
    ]
    | None,
]:
    children = scheduler._children(key.action)
    return children, None if children is None else _admitted_midpoint(
        scheduler, key, children, held, application
    )
