"""Demand bound output carry summaries without constructing future tiles."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal_results import lookup_causal_result
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    causal_interface_key,
    lookup_causal_interface,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.causal_workspace import CausalResults

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.resources.causal_workspace import CausalFrameStack


def supports_reverse_boundary(
    engine: CausalTileEngine,
    before: FieldCellActionID,
    after: FieldCellActionID,
    state: object,
    side: int,
    view: BoundaryTileView,
    anchor: object,
    argument: object,
) -> bool:
    """Admit bounded cold work or a completed deep producer observation."""
    adapter = engine.adapter
    if type(state) is not int or adapter.action_children(after) is not None:
        return False
    consumer = adapter.primitive_law(after)
    producer = adapter.kernels.kernel(adapter._action(before).kernel)
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
    frame: CausalFrame,
    frames: CausalFrameStack,
    values: CausalResults,
) -> bool:
    """Compose required dyadic interface observations in physical order."""
    if frame.op != "reverse_boundary":
        return False
    action, side, view, anchor, argument = frame.args
    workspace = engine.scheduler._causal_workspace
    if frame.stage == 4:
        payload = values.pop()
        summary = payload.bound_reverse_output
        if type(summary) is not ReverseBoundOutput:
            raise ValueError("reverse carry observation returned an incomplete summary")
        engine.ledger.bump("reverse_boundary_single_tile_transfers")
        engine.ledger.bump("reverse_boundary_transfer_completions")
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
                    CausalFrame(
                        "reverse_interface", (action, pieces[0], anchor, argument)
                    ),
                )
            )
            return True
        chunks = workspace.allocate(len(pieces))
        for tile in pieces:
            chunks.append(tile)
        anchors = workspace.allocate(len(chunks) + 1)
        anchors.append(anchor)
        frame.stage, frame.saved = 1, (chunks, argument)
        frames.extend(
            (frame, CausalFrame("scan_chunks", (action, 0, chunks, anchor, 0, anchors)))
        )
    elif frame.stage == 1:
        anchors = values.pop()
        chunks, argument = frame.saved
        arguments = workspace.allocate(len(chunks) + 1)
        arguments.append(argument)
        frame.stage, frame.saved = 2, (chunks, anchors)
        frames.extend(
            (
                frame,
                CausalFrame("scan_chunks", (action, 1, chunks, argument, 0, arguments)),
            )
        )
    elif frame.stage == 2:
        arguments = values.pop()
        arguments.reverse()
        chunks, anchors = frame.saved
        frame.stage, frame.saved = 3, ((chunks, anchors, arguments), 0, None)
        frames.extend(
            (
                frame,
                CausalFrame(
                    "reverse_interface", (action, chunks[0], anchors[0], arguments[1])
                ),
            )
        )
    else:
        payload = values.pop()
        current = payload.bound_reverse_output
        if type(current) is not ReverseBoundOutput:
            raise ValueError("reverse carry observation returned an incomplete summary")
        buffers, index, previous = frame.saved
        summary = current if previous is None else previous.then(current, engine.ledger)
        chunks, anchors, arguments = buffers
        index += 1
        if index == len(chunks):
            chunks.close()
            anchors.close()
            arguments.close()
            engine.ledger.bump("reverse_boundary_transfer_completions")
            values.append(summary)
        else:
            frame.saved = (buffers, index, summary)
            frames.extend(
                (
                    frame,
                    CausalFrame(
                        "reverse_interface",
                        (action, chunks[index], anchors[index], arguments[index + 1]),
                    ),
                )
            )
    return True
