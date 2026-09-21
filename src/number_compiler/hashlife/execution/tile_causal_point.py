"""Parent-first spatial point demand inside the shared causal scheduler."""

from __future__ import annotations

from typing import Any

from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame as _Frame
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.resources.causal_workspace import CausalResults


def point_step(self: Any, frame: _Frame, frames: Any, values: CausalResults) -> bool:
    """Probe a completed parent before requesting its demanded child."""
    if frame.op != "point":
        return False
    a = frame.args
    action, tile, coordinate, base_left, base_right = a
    if frame.stage == 4:
        values.pop()
        values.append(frame.saved[0])
        return True
    if frame.stage in (2, 3):
        if frame.stage == 3:
            emitted = values.pop()
            symbol = self.tiles.resolve(emitted.output).symbol
            if symbol is None:
                raise ValueError("causal point emitted a tile parent")
        else:
            symbol = values.pop()
        if self._application is None:
            values.append(symbol)
            return True
        frame.stage, frame.saved = 4, (symbol,)
        frames.extend(
            (
                frame,
                _Frame(
                    "promote_midpoint",
                    (action, tile, base_left, base_right),
                ),
            )
        )
        return True
    node = self.tiles.resolve(tile)
    if frame.stage == 0:
        if type(coordinate) is not int:
            raise TypeError("causal coordinate requires an exact integer")
        if not 0 <= coordinate < node.width:
            raise IndexError(coordinate)
        self.ledger.bump("tile_causal_point_parent_requests")
        if self._children(action) is None:
            key, completed = probe_causal_result(
                self.scheduler.results,
                action,
                tile,
                PrimitiveCausalPorts(base_left, base_right),
                self._wiring(action),
                action_admission=self._action_admission_token,
            )
        else:
            key = self._composite_key(action, tile, base_left, base_right)
            completed = (
                None
                if key is None
                else lookup_causal_result(
                    self.scheduler.results,
                    key,
                    action_admission=self._action_admission_token,
                )
            )
        if completed is not None:
            symbol = self.tiles.point(completed.output, coordinate)
            if self._application is None:
                self._result_leases.append(completed)
            else:
                self.scheduler._pin_causal(self._application, key, completed)
            self.ledger.bump("tile_causal_point_parent_hits")
            values.append(symbol)
            return True
        if (
            node.first_active is None
            and quiescent_boundary(
                self,
                action,
                0,
                BoundaryTileView(tile, 0, node.width),
                base_left,
                base_right,
                discharged_extent=1,
            )
            is not None
        ):
            values.append(self.tiles.alphabet(node.alphabet).blank)
            self.ledger.bump("behavior_point_observations")
            return True
        if not node.level:
            frame.stage = 3
            frames.extend(
                (
                    frame,
                    _Frame("output", (action, tile, base_left, base_right)),
                )
            )
            return True
        if node.left is None or node.right is None:
            raise ValueError("causal point parent omitted its children")
        side = int(coordinate >= node.width // 2)
        sibling = node.left if side else node.right
        incoming = base_left if side else base_right
        frame.stage = 1
        frames.extend(
            (
                frame,
                _Frame(
                    "advance",
                    (
                        action,
                        1 - side,
                        incoming,
                        BoundaryTileView(
                            sibling,
                            0,
                            node.width // 2,
                            1 - side,
                        ),
                    ),
                ),
            )
        )
        return True
    transferred = values.pop()
    if node.left is None or node.right is None:
        raise ValueError("causal point parent omitted its children")
    side = int(coordinate >= node.width // 2)
    child = node.right if side else node.left
    child_left, child_right = (
        (transferred, base_right) if side else (base_left, transferred)
    )
    frame.stage = 2
    self.ledger.bump("tile_causal_point_demanded_descents")
    frames.extend(
        (
            frame,
            _Frame(
                "point",
                (
                    action,
                    child,
                    coordinate - side * (node.width // 2),
                    child_left,
                    child_right,
                ),
            ),
        )
    )
    return True
