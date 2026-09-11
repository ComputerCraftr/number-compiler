"""Cached-midpoint task step for the iterative causal recurrence."""

from __future__ import annotations

from typing import Any

from number_compiler.resources.causal_workspace import CausalResults

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    PrimitiveCausalPorts,
    causal_result_key,
    lookup_causal_result,
    publish_causal_completed,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
    result_payload,
    temporal_payload,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileID


def cached_midpoint_step(
    engine: Any,
    frame: CausalFrame,
    frames: Any,
    values: CausalResults,
    action: FieldCellActionID,
    tile: TileID,
    left: object,
    right: object,
    children: tuple[FieldCellActionID, FieldCellActionID],
) -> bool:
    """Consume an already completed first temporal child, never compute a miss."""
    before, after = children
    if frame.stage == 0:
        frame.stage = 10
        frames.extend(
            (
                frame,
                CausalFrame("anchor", (before, 1, right)),
                CausalFrame("anchor", (before, 0, left)),
            )
        )
        return True
    if frame.stage == 10:
        right_anchor, left_anchor = values.pop(), values.pop()
        before_key: PoweredResultKey | None
        if type(left_anchor) is int and type(right_anchor) is int:
            before_key = causal_result_key(
                engine.scheduler.results,
                before,
                tile,
                PrimitiveCausalPorts(left_anchor, right_anchor),
                engine.adapter.wiring(before),
            )
        else:
            before_key = engine._composite_key(before, tile, left_anchor, right_anchor)
        completed = (
            None
            if before_key is None
            else lookup_causal_result(engine.scheduler.results, before_key)
        )
        if completed is None:
            frame.stage = 20
            frames.append(frame)
            return True
        first = result_payload(engine.tiles, completed)
        if engine._application is None:
            engine._result_leases.append(completed)
        else:
            engine.scheduler._pin_causal(engine._application, before_key, completed)
        node = engine.tiles.resolve(tile)
        frame.stage, frame.saved = 13, (first,)
        if type(left_anchor) is int and type(right_anchor) is int:
            # A completed primitive result already owns both directed exits.
            # Re-scanning its input to recover them defeats complete-result reuse.
            exits = first.semantics.outgoing_ports
            if len(exits) != 2:
                raise ValueError("completed primitive midpoint omitted directed exits")
            frames.append(frame)
            values.append(exits[0])
            values.append(exits[1])
            engine.ledger.bump("tile_causal_midpoint_port_reuses")
            engine.ledger.bump("tile_causal_midpoint_reuse")
            return True
        frames.extend(
            (
                frame,
                CausalFrame(
                    "advance",
                    (
                        before,
                        1,
                        right_anchor,
                        BoundaryTileView(tile, 0, node.width, 1),
                    ),
                ),
                CausalFrame(
                    "advance",
                    (
                        before,
                        0,
                        left_anchor,
                        BoundaryTileView(tile, 0, node.width),
                    ),
                ),
            )
        )
        engine.ledger.bump("tile_causal_midpoint_reuse")
        return True
    if frame.stage == 13:
        right_argument, left_argument = values.pop(), values.pop()
        frame.stage = 11
        frames.extend(
            (
                frame,
                CausalFrame("residual", (action, 1, right, left_argument)),
                CausalFrame("residual", (action, 0, left, right_argument)),
            )
        )
        return True
    if frame.stage == 11:
        right_state, left_state = values.pop(), values.pop()
        frame.stage = 12
        frames.extend(
            (
                frame,
                CausalFrame(
                    "output",
                    (after, frame.saved[0].output, left_state, right_state),
                ),
            )
        )
        return True
    if frame.stage == 12:
        second = values.pop()
        first = frame.saved[0]
        if not isinstance(first, CausalCompletedOutput) or not isinstance(
            second, CausalCompletedOutput
        ):
            raise AssertionError("cached temporal edge returned another result sort")
        if not isinstance(left, CausalPrefix) or not isinstance(right, CausalPrefix):
            raise ValueError("cached temporal edge requires exact causal prefixes")
        payload = temporal_payload(
            engine.adapter,
            before,
            after,
            first,
            second,
            left.explicit_edge or right.explicit_edge,
        )
        key = engine._composite_key(action, tile, left, right)
        if key is not None:
            completed = publish_causal_completed(engine.scheduler.results, key, payload)
            payload = result_payload(engine.tiles, completed)
            if engine._application is None:
                engine._result_leases.append(completed)
            else:
                engine.scheduler._pin_causal(engine._application, key, completed)
            engine.ledger.bump("tile_causal_result_evaluations")
            engine.ledger.bump("tile_temporal_complete_compositions")
        values.append(payload)
        return True
    if frame.stage == 20:
        frame.stage = 0
        return False
    return False


__all__ = ["cached_midpoint_step"]
