"""Store-free demanded tiles operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
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
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileID

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
    boundaries: BoundaryTileOperands = BoundaryTileOperands(),
    fusion: FusedBoundaryContract | None = None,
) -> int:
    if type(coordinate) is not int:
        raise TypeError("tile coordinate requires an exact integer")
    root = self.tiles.resolve(source)
    if not 0 <= coordinate < root.width:
        raise IndexError(coordinate)
    self._validate_execution_key(
        self._key(action, source, ports, wiring, boundaries, fusion)
    )
    action_now, tile_now, ports_now, wiring_now = action, source, ports, wiring
    held: list[ResultLease] = []
    try:
        while True:
            self._workspace_peak(len(held) + 1)
            self.ledger.bump("tile_scheduler_demand_descents")
            key = self._key(
                action_now, tile_now, ports_now, wiring_now, boundaries, fusion
            )
            self._validate_execution_key(key)
            found = self.results.lookup(key)
            if found is not None:
                self.ledger.bump("tile_scheduler_demand_parent_hits")
                output = found.output
                if _application is None:
                    held.append(found)
                else:
                    self._pin(_application, key, found)
                return self.tiles.point(output, coordinate)
            self.ledger.bump("tile_scheduler_demand_parent_misses")
            from number_compiler.hashlife.execution.tile_causal_entry import (
                causal_point,
            )

            causal = causal_point(self, key, coordinate, application=_application)
            if causal is not None:
                return causal
            children = self._children(action_now)
            if children is not None:
                producer = before_context(self, key, children[0])
                before_key = self._key(
                    children[0],
                    tile_now,
                    producer.ports,
                    producer.wiring,
                    producer.boundaries,
                )
                midpoint = self.results.lookup(before_key)
                if midpoint is not None:
                    self.ledger.bump("tile_scheduler_midpoint_hits")
                    context = after_context(self, key, children[1], midpoint.result)
                    output = midpoint.output
                    if _application is None:
                        held.append(midpoint)
                    else:
                        self._pin(
                            _application,
                            before_key,
                            midpoint,
                        )
                    action_now, tile_now = children[1], output
                    ports_now, wiring_now = context.ports, context.wiring
                    boundaries, fusion = context.boundaries, None
                    continue
                from number_compiler.hashlife.execution.tile_fused import (
                    demanded_fused_point,
                )

                fused = demanded_fused_point(self, key, coordinate)
                if fused is not None:
                    return fused
            node = self.tiles.resolve(tile_now)
            if not node.level:
                result = self._complete_leaf(key)
                output = result.output
                if _application is None:
                    held.append(result)
                else:
                    self._pin(_application, key, result)
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
    boundaries: BoundaryTileOperands = BoundaryTileOperands(),
    fusion: FusedBoundaryContract | None = None,
) -> int:
    root = self.tiles.resolve(source)
    stop = root.width if limit is None else limit
    if type(stop) is not int:
        raise TypeError("tile width limit requires an exact integer")
    if not 0 <= stop <= root.width:
        raise ValueError("tile width limit lies outside the source")
    self._validate_execution_key(
        self._key(action, source, ports, wiring, boundaries, fusion)
    )
    if not stop:
        return 0
    action_now, tile_now, ports_now, wiring_now = action, source, ports, wiring
    offset = 0
    remaining = stop
    held: list[ResultLease] = []
    initial_request = True
    try:
        while True:
            self._workspace_peak(len(held) + 1)
            self.ledger.bump("tile_scheduler_width_descents")
            key = self._key(
                action_now, tile_now, ports_now, wiring_now, boundaries, fusion
            )
            self._validate_execution_key(key)
            found = self.results.lookup(key)
            if found is not None:
                self.ledger.bump("tile_scheduler_demand_parent_hits")
                output = found.output
                if _application is None:
                    held.append(found)
                else:
                    self._pin(_application, key, found)
                return offset + self.tiles.active_width(output, remaining)
            self.ledger.bump("tile_scheduler_demand_parent_misses")
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
                    self.ledger.bump("reverse_current_growth_width_shortcuts")
                    return min(remaining, root.extent + growth)
            initial_request = False
            from number_compiler.hashlife.execution.tile_causal_entry import (
                causal_width_query,
            )

            causal = causal_width_query(self, key, remaining, application=_application)
            if causal is not None:
                return offset + causal
            children = self._children(action_now)
            if children is not None:
                producer = before_context(self, key, children[0])
                before_key = self._key(
                    children[0],
                    tile_now,
                    producer.ports,
                    producer.wiring,
                    producer.boundaries,
                )
                midpoint = self.results.lookup(before_key)
                if midpoint is not None:
                    self.ledger.bump("tile_scheduler_midpoint_hits")
                    context = after_context(self, key, children[1], midpoint.result)
                    output = midpoint.output
                    if _application is None:
                        held.append(midpoint)
                    else:
                        self._pin(
                            _application,
                            before_key,
                            midpoint,
                        )
                    action_now, tile_now = children[1], output
                    ports_now, wiring_now = context.ports, context.wiring
                    boundaries, fusion = context.boundaries, None
                    continue
                from number_compiler.hashlife.execution.tile_fused import (
                    demanded_fused_width,
                )

                fused = demanded_fused_width(self, key, remaining)
                if fused is not None:
                    return offset + fused
            node = self.tiles.resolve(tile_now)
            if not node.level:
                result = self._complete_leaf(key)
                output = result.output
                if _application is None:
                    held.append(result)
                else:
                    self._pin(_application, key, result)
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
    boundaries: BoundaryTileOperands = BoundaryTileOperands(),
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
