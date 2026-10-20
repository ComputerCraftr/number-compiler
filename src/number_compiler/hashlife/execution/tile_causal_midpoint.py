"""Cached-midpoint task step for the iterative causal recurrence."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    AnchorFrame,
    CausalTaskFrame,
    OutputFrame,
    ResidualFrame,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    publish_composite_output,
    retain_completed,
    temporal_payload,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalPrefix,
    CausalState,
    CausalTaskValue,
    pop_causal_state,
    pop_completed_output,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


@dataclass(frozen=True, slots=True)
class _MidpointParentHit:
    key: PoweredResultKey
    completed: CausalCompletedOutput
    primitive: bool


def consume_midpoint_parent(
    engine: CausalTileEngine,
    before: FieldCellActionID,
    tile: TileID,
    left_anchor: CausalState,
    right_anchor: CausalState,
) -> _MidpointParentHit | None:
    """Probe and lease the already completed first temporal child once."""
    key: PoweredResultKey | None
    if type(left_anchor) is int and type(right_anchor) is int:
        key, completed = probe_causal_result(
            engine.scheduler.results,
            before,
            tile,
            PrimitiveCausalPorts(left_anchor, right_anchor),
            engine.result_wiring(before),
            action_admission=engine.action_admission,
        )
    else:
        key = engine.composite_key(before, tile, left_anchor, right_anchor)
        completed = (
            None
            if key is None
            else lookup_causal_result(
                engine.scheduler.results,
                key,
                action_admission=engine.action_admission,
            )
        )
    if completed is None:
        return None
    if key is None:
        raise AssertionError("completed midpoint parent omitted its exact key")
    return _MidpointParentHit(
        key,
        retain_completed(engine, key, completed),
        type(left_anchor) is int and type(right_anchor) is int,
    )


def cached_midpoint_step(
    engine: CausalTileEngine,
    frame: OutputFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
    action: FieldCellActionID,
    tile: TileID,
    left: CausalState,
    right: CausalState,
    children: tuple[FieldCellActionID, FieldCellActionID],
) -> bool:
    """Consume an already completed first temporal child, never compute a miss."""
    before, after = children
    if frame.stage == 0:
        frame.stage = 10
        frames.extend(
            (
                frame,
                AnchorFrame((before, 1, right)),
                AnchorFrame((before, 0, left)),
            )
        )
        return True
    if frame.stage == 10:
        right_anchor = pop_causal_state(values)
        left_anchor = pop_causal_state(values)
        parent_hit = consume_midpoint_parent(
            engine, before, tile, left_anchor, right_anchor
        )
        if parent_hit is None:
            frame.stage = 20
            frames.append(frame)
            return True
        first = parent_hit.completed
        node = engine.tiles.resolve(tile)
        frame.stage, frame.saved = 13, (first,)
        if parent_hit.primitive:
            # A completed primitive result already owns both directed exits.
            # Re-scanning its input to recover them defeats complete-result reuse.
            exits = first.semantics.outgoing_ports
            if len(exits) != 2:
                raise ValueError("completed primitive midpoint omitted directed exits")
            frames.append(frame)
            values.append(exits[0])
            values.append(exits[1])
            engine.ledger.bump(_execution_keys.TILE_CAUSAL_MIDPOINT_PORT_REUSES)
            engine.ledger.bump(_execution_keys.TILE_CAUSAL_MIDPOINT_REUSE)
            return True
        frames.extend(
            (
                frame,
                AdvanceFrame(
                    (
                        before,
                        1,
                        right_anchor,
                        BoundaryTileView(tile, 0, node.width, 1),
                    ),
                ),
                AdvanceFrame(
                    (
                        before,
                        0,
                        left_anchor,
                        BoundaryTileView(tile, 0, node.width),
                    ),
                ),
            )
        )
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_MIDPOINT_REUSE)
        return True
    if frame.stage == 13:
        right_argument = pop_causal_state(values)
        left_argument = pop_causal_state(values)
        frame.stage = 11
        frames.extend(
            (
                frame,
                ResidualFrame((action, 1, right, left_argument)),
                ResidualFrame((action, 0, left, right_argument)),
            )
        )
        return True
    if frame.stage == 11:
        right_state = pop_causal_state(values)
        left_state = pop_causal_state(values)
        frame.stage = 12
        match frame.saved:
            case (CausalCompletedOutput() as first,):
                frames.extend(
                    (
                        frame,
                        OutputFrame((after, first.output, left_state, right_state)),
                    )
                )
            case _:
                raise AssertionError("cached midpoint lost its completed child")
        return True
    if frame.stage == 12:
        second = pop_completed_output(values)
        match frame.saved:
            case (CausalCompletedOutput() as first,):
                pass
            case _:
                raise AssertionError("cached midpoint lost its completed child")
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
        payload = publish_composite_output(engine, action, tile, left, right, payload)
        values.append(payload)
        return True
    if frame.stage == 20:
        frame.stage = 0
        return False
    return False


__all__ = ["cached_midpoint_step"]
