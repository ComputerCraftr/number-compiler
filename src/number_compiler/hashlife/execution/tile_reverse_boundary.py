"""Demand bound output carry summaries without constructing future tiles."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.causal_frames import (
    CausalTaskFrame,
    ReverseBoundaryFrame,
    ReverseInterfaceFrame,
)
from number_compiler.hashlife.execution.tile_causal_results import lookup_causal_result
from number_compiler.hashlife.execution.tile_causal_tasks import (
    schedule_reflected_scan,
    schedule_spatial_scan,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    causal_interface_key,
    lookup_causal_interface,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalState,
    CausalTaskValue,
    pop_interface_payload,
    pop_spatial_buffer,
    require_spatial_buffer,
    spatial_buffer_state_at,
    spatial_buffer_tile_at,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def supports_reverse_boundary(
    engine: CausalTileEngine,
    before: FieldCellActionID,
    after: FieldCellActionID,
    state: CausalState,
    side: int,
    view: BoundaryTileView,
    anchor: CausalState,
    argument: CausalState,
) -> bool:
    """Admit bounded cold work or a completed deep producer observation."""
    adapter = engine.adapter
    if type(state) is not int or adapter.action_children(after) is not None:
        return False
    consumer = adapter.primitive_law(after)
    producer = adapter.kernels.kernel(adapter.action_record(before).kernel)
    supported = (
        type(consumer.effect) in (BaseBlockEffect, DigitNormalizeBlockEffect)
        and type(producer.effect) is BaseBlockEffect
        and consumer.base == producer.base
        and 2 <= consumer.base <= 15
    )
    if not supported:
        return False
    children = adapter.action_children(before)
    if children is None or all(
        adapter.action_children(child) is None for child in children
    ):
        return True
    pieces = engine._covered_chunks(view)
    if len(pieces) != 1:
        return False
    tile = pieces[0]
    left, right = anchor, argument
    if side:
        tile = engine._keep(engine.tiles.mirror(tile))
        left, right = right, left
    key = engine._composite_key(before, tile, left, right)
    if key is None:
        return False
    completed = lookup_causal_result(engine.scheduler.results, key)
    if completed is not None:
        completed.close()
        return True
    return (
        lookup_causal_interface(
            engine.scheduler.results,
            causal_interface_key(key, observation="reverse-output-carry"),
        )
        is not None
    )


def reverse_boundary_step(
    engine: CausalTileEngine,
    frame: ReverseBoundaryFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
) -> bool:
    """Compose required dyadic interface observations in physical order."""
    action, side, view, anchor, argument = frame.args
    workspace = engine.scheduler._causal_workspace
    if frame.stage == 4:
        payload = pop_interface_payload(values)
        summary = payload.bound_reverse_output
        if type(summary) is not ReverseBoundOutput:
            raise ValueError("reverse carry observation returned an incomplete summary")
        engine.ledger.bump(_execution_keys.REVERSE_BOUNDARY_SINGLE_TILE_TRANSFERS)
        engine.ledger.bump(_execution_keys.REVERSE_BOUNDARY_TRANSFER_COMPLETIONS)
        values.append(summary)
        return True
    if frame.stage == 0:
        pieces = engine._covered_chunks(view)
        if side:
            pieces = tuple(
                engine._keep(engine.tiles.mirror(tile)) for tile in reversed(pieces)
            )
            anchor, argument = argument, anchor
        if not pieces:
            raise ValueError("reverse output transfer requires a nonempty region")
        if len(pieces) == 1:
            # There is no internal spatial midpoint. The interval's two
            # exterior contexts already are the inputs to its sole interface;
            # scanning that same interval in both directions computes exits
            # which the single-piece composition never consumes.
            frame.stage = 4
            frames.extend(
                (
                    frame,
                    ReverseInterfaceFrame((action, pieces[0], anchor, argument)),
                )
            )
            return True
        source_chunks = workspace.allocate(len(pieces))
        for tile in pieces:
            source_chunks.append(tile)
        frame.saved = (source_chunks, argument)
        schedule_spatial_scan(
            workspace, frames, frame, action, 0, source_chunks, anchor
        )
    elif frame.stage == 1:
        schedule_reflected_scan(workspace, frames, frame, action, values)
    elif frame.stage == 2:
        arguments = pop_spatial_buffer(values)
        arguments.reverse()
        match frame.saved:
            case (chunks_value, anchors_value):
                chunks = require_spatial_buffer(chunks_value)
                anchors = require_spatial_buffer(anchors_value)
            case _:
                raise AssertionError("reverse boundary reflection lost its anchors")
        frame.stage, frame.saved = 3, ((chunks, anchors, arguments), 0, None)
        frames.extend(
            (
                frame,
                ReverseInterfaceFrame(
                    (
                        action,
                        spatial_buffer_tile_at(chunks, 0),
                        spatial_buffer_state_at(anchors, 0),
                        spatial_buffer_state_at(arguments, 1),
                    )
                ),
            )
        )
    else:
        payload = pop_interface_payload(values)
        current = payload.bound_reverse_output
        if type(current) is not ReverseBoundOutput:
            raise ValueError("reverse carry observation returned an incomplete summary")
        match frame.saved:
            case ((chunks_value, anchors_value, arguments_value), index, previous):
                chunks = require_spatial_buffer(chunks_value)
                anchors = require_spatial_buffer(anchors_value)
                arguments = require_spatial_buffer(arguments_value)
                if type(index) is not int:
                    raise AssertionError("reverse boundary lost its transfer index")
                if previous is not None and type(previous) is not ReverseBoundOutput:
                    raise AssertionError("reverse boundary lost its prior summary")
            case _:
                raise AssertionError("reverse boundary lost its transfer cursor")
        summary = current if previous is None else previous.then(current, engine.ledger)
        index += 1
        if index == len(chunks):
            chunks.close()
            anchors.close()
            arguments.close()
            engine.ledger.bump(_execution_keys.REVERSE_BOUNDARY_TRANSFER_COMPLETIONS)
            values.append(summary)
        else:
            frame.saved = ((chunks, anchors, arguments), index, summary)
            frames.extend(
                (
                    frame,
                    ReverseInterfaceFrame(
                        (
                            action,
                            spatial_buffer_tile_at(chunks, index),
                            spatial_buffer_state_at(anchors, index),
                            spatial_buffer_state_at(arguments, index + 1),
                        )
                    ),
                )
            )
    return True
