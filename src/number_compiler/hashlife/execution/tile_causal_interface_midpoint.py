"""Completed-midpoint reuse for output-free causal interface observations."""

from __future__ import annotations

from dataclasses import replace
from typing import Any

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    result_payload,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    publish_causal_interface,
)
from number_compiler.hashlife.tiles.tile_result_records import CausalInterfaceKey
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_workspace import CausalResults


def cached_midpoint_interface_step(
    engine: Any,
    frame: CausalFrame,
    frames: Any,
    values: CausalResults,
    action: FieldCellActionID,
    tile: TileID,
    left: object,
    right: object,
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
                CausalFrame("anchor", (before, 1, right)),
                CausalFrame("anchor", (before, 0, left)),
            )
        )
        return True
    if frame.stage == 30:
        right_anchor, left_anchor = values.pop(), values.pop()
        if type(left_anchor) is int and type(right_anchor) is int:
            before_key, completed = probe_causal_result(
                engine.scheduler.results,
                before,
                tile,
                PrimitiveCausalPorts(left_anchor, right_anchor),
                engine._wiring(before),
                action_admission=engine._action_admission_token,
            )
        else:
            before_key = engine._composite_key(
                before,
                tile,
                left_anchor,
                right_anchor,
            )
            completed = (
                None
                if before_key is None
                else lookup_causal_result(
                    engine.scheduler.results,
                    before_key,
                    action_admission=engine._action_admission_token,
                )
            )
        if completed is None:
            frame.stage = 0
            return False
        first = result_payload(engine.tiles, completed)
        if engine._application is None:
            engine._result_leases.append(completed)
        else:
            engine.scheduler._pin_causal(engine._application, before_key, completed)
        node = engine.tiles.resolve(tile)
        frame.stage, frame.saved = 31, (first, observation_key)
        if type(left_anchor) is int and type(right_anchor) is int:
            exits = first.semantics.outgoing_ports
            if len(exits) != 2:
                raise ValueError("completed primitive midpoint omitted directed exits")
            frames.append(frame)
            values.append(exits[0])
            values.append(exits[1])
            engine.ledger.bump("tile_causal_midpoint_port_reuses")
            engine.ledger.bump("tile_causal_interface_midpoint_reuse")
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
        engine.ledger.bump("tile_causal_interface_midpoint_reuse")
        return True
    if frame.stage == 31:
        right_argument, left_argument = values.pop(), values.pop()
        frame.stage = 32
        frames.extend(
            (
                frame,
                CausalFrame("residual", (action, 1, right, left_argument)),
                CausalFrame("residual", (action, 0, left, right_argument)),
            )
        )
        return True
    if frame.stage == 32:
        right_state, left_state = values.pop(), values.pop()
        frame.stage = 33
        frames.extend(
            (
                frame,
                CausalFrame(
                    "interface",
                    (after, frame.saved[0].output, left_state, right_state),
                ),
            )
        )
        return True
    if frame.stage != 33:
        return False
    second = values.pop()
    first, saved_key = frame.saved
    match (first, second):
        case (CausalCompletedOutput(), CausalInterfacePayload()):
            pass
        case _:
            raise AssertionError("cached interface edge returned another result sort")
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
        "causal_interface_result_publications", 0
    )
    values.append(
        publish_causal_interface(
            engine.scheduler.results,
            saved_key,
            payload,
        )
    )
    publications_after = engine.ledger.counters.get(
        "causal_interface_result_publications", 0
    )
    if publications_after > publications_before:
        engine.ledger.bump(
            "tile_causal_interface_midpoint_publications",
            publications_after - publications_before,
        )
    return True


__all__ = ["cached_midpoint_interface_step"]
