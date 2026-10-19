"""Parent-first spatial point demand inside the shared causal scheduler."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    CausalTaskFrame,
    OutputFrame,
    PointFrame,
    PromoteMidpointFrame,
)
from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalTaskValue,
    pop_boolean,
    pop_causal_state,
    pop_completed_output,
    pop_exact_integer,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def point_step(
    self: CausalTileEngine,
    frame: PointFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
) -> bool:
    """Probe a completed parent before requesting its demanded child."""
    a = frame.args
    action, tile, coordinate, base_left, base_right = a
    if frame.stage == 4:
        pop_boolean(values)
        match frame.saved:
            case (symbol,):
                values.append(symbol)
            case _:
                raise AssertionError("causal point lost its emitted symbol")
        return True
    if frame.stage in (2, 3):
        if frame.stage == 3:
            emitted = pop_completed_output(values)
            emitted_symbol = self.tiles.resolve(emitted.output).symbol
            if emitted_symbol is None:
                raise ValueError("causal point emitted a tile parent")
            symbol = emitted_symbol
        else:
            symbol = pop_exact_integer(values)
        if self._application is None:
            values.append(symbol)
            return True
        frame.stage, frame.saved = 4, (symbol,)
        frames.extend(
            (
                frame,
                PromoteMidpointFrame(
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
        self.ledger.bump(_execution_keys.TILE_CAUSAL_POINT_PARENT_REQUESTS)
        key: PoweredResultKey | None
        if self._children(action) is None:
            if type(base_left) is not int or type(base_right) is not int:
                raise TypeError("primitive causal point requires exact boundary ports")
            key, completed = probe_causal_result(
                self.scheduler.results,
                action,
                tile,
                PrimitiveCausalPorts(base_left, base_right),
                self._wiring(action),
                action_admission=self.action_admission,
            )
        else:
            key = self._composite_key(action, tile, base_left, base_right)
            completed = (
                None
                if key is None
                else lookup_causal_result(
                    self.scheduler.results,
                    key,
                    action_admission=self.action_admission,
                )
            )
        if completed is not None:
            if key is None:
                raise AssertionError("completed causal result has no request key")
            symbol = self.tiles.point(completed.output, coordinate)
            if self._application is None:
                self._result_leases.append(completed)
            else:
                self.scheduler._pin_causal(self._application, key, completed)
            self.ledger.bump(_execution_keys.TILE_CAUSAL_POINT_PARENT_HITS)
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
            self.ledger.bump(_execution_keys.BEHAVIOR_POINT_OBSERVATIONS)
            return True
        if not node.level:
            frame.stage = 3
            frames.extend(
                (
                    frame,
                    OutputFrame((action, tile, base_left, base_right)),
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
                AdvanceFrame(
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
    transferred = pop_causal_state(values)
    if node.left is None or node.right is None:
        raise ValueError("causal point parent omitted its children")
    side = int(coordinate >= node.width // 2)
    child = node.right if side else node.left
    child_left, child_right = (
        (transferred, base_right) if side else (base_left, transferred)
    )
    frame.stage = 2
    self.ledger.bump(_execution_keys.TILE_CAUSAL_POINT_DEMANDED_DESCENTS)
    frames.extend(
        (
            frame,
            PointFrame(
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
