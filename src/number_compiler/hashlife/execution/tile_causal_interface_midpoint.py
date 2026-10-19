"""Completed-midpoint reuse for output-free causal interface observations."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    AnchorFrame,
    CausalTaskFrame,
    InterfaceFrame,
    ResidualFrame,
    ReverseInterfaceFrame,
)
from number_compiler.hashlife.execution.tile_causal_midpoint import (
    consume_midpoint_parent,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    publish_causal_interface,
)
from number_compiler.hashlife.tiles.tile_result_records import CausalInterfaceKey
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalState,
    CausalTaskValue,
    pop_causal_state,
    pop_interface_payload,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def cached_midpoint_interface_step(
    engine: CausalTileEngine,
    frame: InterfaceFrame | ReverseInterfaceFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
    action: FieldCellActionID,
    tile: TileID,
    left: CausalState,
    right: CausalState,
    children: tuple[FieldCellActionID, FieldCellActionID],
    observation_key: CausalInterfaceKey | None,
) -> bool:
    """Consume an existing producer tile; return false immediately on a miss."""
    before, after = children
    if frame.stage == 0:
        frame.stage = 30
        frames.extend(
            (
                frame,
                AnchorFrame((before, 1, right)),
                AnchorFrame((before, 0, left)),
            )
        )
        return True
    if frame.stage == 30:
        right_anchor = pop_causal_state(values)
        left_anchor = pop_causal_state(values)
        parent_hit = consume_midpoint_parent(
            engine, before, tile, left_anchor, right_anchor
        )
        if parent_hit is None:
            frame.stage = 0
            return False
        first = parent_hit.completed
        node = engine.tiles.resolve(tile)
        frame.stage, frame.saved = 31, (first, observation_key)
        if parent_hit.primitive:
            exits = first.semantics.outgoing_ports
            if len(exits) != 2:
                raise ValueError("completed primitive midpoint omitted directed exits")
            frames.append(frame)
            values.append(exits[0])
            values.append(exits[1])
            engine.ledger.bump(_execution_keys.TILE_CAUSAL_MIDPOINT_PORT_REUSES)
            engine.ledger.bump(_execution_keys.TILE_CAUSAL_INTERFACE_MIDPOINT_REUSE)
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
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_INTERFACE_MIDPOINT_REUSE)
        return True
    if frame.stage == 31:
        right_argument = pop_causal_state(values)
        left_argument = pop_causal_state(values)
        frame.stage = 32
        frames.extend(
            (
                frame,
                ResidualFrame((action, 1, right, left_argument)),
                ResidualFrame((action, 0, left, right_argument)),
            )
        )
        return True
    if frame.stage == 32:
        right_state = pop_causal_state(values)
        left_state = pop_causal_state(values)
        frame.stage = 33
        match frame.saved:
            case (CausalCompletedOutput() as first, _observation_key):
                frames.extend(
                    (
                        frame,
                        InterfaceFrame((after, first.output, left_state, right_state)),
                    )
                )
            case _:
                raise AssertionError("cached interface midpoint lost its parent")
        return True
    if frame.stage != 33:
        return False
    second = pop_interface_payload(values)
    match frame.saved:
        case (CausalCompletedOutput() as first, saved_key):
            pass
        case _:
            raise AssertionError("cached interface midpoint lost its result key")
    from number_compiler.hashlife.execution.tile_physical_support import (
        temporal_physical_support,
    )

    payload = replace(
        second,
        physical_ticks=first.semantics.physical_ticks + second.physical_ticks,
        event_weight=first.semantics.event_weight + second.event_weight,
        frame_shift=first.semantics.frame_shift + second.frame_shift,
        physical_support=temporal_physical_support(
            first.semantics.physical_support,
            second.physical_support,
            before_ticks=first.semantics.physical_ticks,
            after_ticks=second.physical_ticks,
        ),
    )
    if saved_key is None:
        values.append(payload)
        return True
    publications_before = engine.ledger.counters.get(
        _shared_keys.CAUSAL_INTERFACE_RESULT_PUBLICATIONS, 0
    )
    values.append(
        publish_causal_interface(
            engine.scheduler.results,
            saved_key,
            payload,
        )
    )
    publications_after = engine.ledger.counters.get(
        _shared_keys.CAUSAL_INTERFACE_RESULT_PUBLICATIONS, 0
    )
    if publications_after > publications_before:
        engine.ledger.bump(
            _execution_keys.TILE_CAUSAL_INTERFACE_MIDPOINT_PUBLICATIONS,
            publications_after - publications_before,
        )
    return True


__all__ = ["cached_midpoint_interface_step"]
