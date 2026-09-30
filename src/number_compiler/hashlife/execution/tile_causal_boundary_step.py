"""Dyadic causal boundary tasks; spatial work is allocated once per request."""

from __future__ import annotations

from typing import Any

from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    schedule_reflected_scan,
    schedule_spatial_scan,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_boundary_concat_memo import (
    concat_cached_boundary_views,
)
from number_compiler.resources.causal_workspace import CausalResults


def probe_boundary_result(engine: Any, frame: CausalFrame) -> BoundaryTileView | None:
    """Reuse an already completed dyadic boundary before either sibling scan."""
    action, side, view, anchor, argument = frame.args
    pieces = engine._covered_chunks(view)
    if side:
        pieces = tuple(
            engine._keep(engine.tiles.mirror(tile)) for tile in reversed(pieces)
        )
        anchor, argument = argument, anchor
    engine.ledger.bump("tile_causal_boundary_output_piece_normalizations", len(pieces))
    if len(pieces) != 1:
        chunks = engine.scheduler._causal_workspace.allocate(len(pieces))
        for tile in pieces:
            chunks.append(tile)
        frame.saved = (chunks, anchor, argument)
        return None
    tile = pieces[0]
    if engine._children(action) is None:
        if type(anchor) is not int or type(argument) is not int:
            raise TypeError("primitive boundary requires finite endpoints")
        key, completed = probe_causal_result(
            engine.scheduler.results,
            action,
            tile,
            PrimitiveCausalPorts(anchor, argument),
            engine._wiring(action),
            action_admission=engine._action_admission_token,
        )
    else:
        key = engine._composite_key(action, tile, anchor, argument)
        completed = (
            None
            if key is None
            else lookup_causal_result(
                engine.scheduler.results,
                key,
                action_admission=engine._action_admission_token,
            )
        )
    if completed is None:
        chunks = engine.scheduler._causal_workspace.allocate(1)
        chunks.append(tile)
        frame.saved = (chunks, anchor, argument)
        return None
    output = completed.output
    if engine._application is None:
        engine._result_leases.append(completed)
    else:
        engine.scheduler._pin_causal(engine._application, key, completed)
    if side:
        output = engine._keep(engine.tiles.mirror(output))
    engine.ledger.bump("tile_causal_boundary_completed_parent_hits")
    return BoundaryTileView(output, 0, view.relative_extent)


def boundary_step(
    engine: Any, frame: CausalFrame, frames: Any, values: CausalResults
) -> bool:
    op, args = frame.op, frame.args
    workspace = engine.scheduler._causal_workspace
    if op == "scan_chunks":
        action, side, chunks, current, index, states = args
        if frame.stage == 0:
            if index == len(chunks):
                values.append(states)
                return True
            frame.stage = 1
            tile = chunks[len(chunks) - index - 1 if side else index]
            width = engine.tiles.resolve(tile).width
            frames.extend(
                (
                    frame,
                    CausalFrame(
                        "advance",
                        (
                            action,
                            side,
                            current,
                            BoundaryTileView(tile, 0, width, side),
                        ),
                    ),
                )
            )
        else:
            nxt = values.pop()
            states.append(nxt)
            frames.append(
                CausalFrame(
                    "scan_chunks", (action, side, chunks, nxt, index + 1, states)
                )
            )
        return True
    if op == "output_chunk_list":
        action, chunks, anchors, arguments, index, outputs = args
        if frame.stage == 0:
            if index == len(chunks):
                anchors.close()
                arguments.close()
                values.append(outputs)
                return True
            frame.stage = 1
            frames.extend(
                (
                    frame,
                    CausalFrame(
                        "output",
                        (
                            action,
                            chunks[index],
                            anchors[index],
                            arguments[index + 1],
                        ),
                    ),
                )
            )
        else:
            outputs.append(values.pop().output)
            frames.append(
                CausalFrame(
                    "output_chunk_list",
                    (
                        action,
                        chunks,
                        anchors,
                        arguments,
                        index + 1,
                        outputs,
                    ),
                )
            )
        return True
    if op != "output_boundary":
        return False
    action, side, view, anchor, argument = args
    if frame.stage == 4:
        completed = values.pop()
        (chunks,) = frame.saved
        output = completed.output
        output = engine._keep(
            engine.tiles.mirror(output) if side else engine.tiles.retain(output)
        )
        chunks.close()
        values.append(BoundaryTileView(output, 0, view.relative_extent))
        engine.ledger.bump("tile_causal_boundary_single_tile_outputs")
        engine.ledger.bump("tile_causal_boundary_output_completions")
        return True
    if frame.stage == 0:
        # Normalize once, not again after each child task returns.
        chunks, anchor, argument = frame.saved
        if len(chunks) == 1:
            # One dyadic interval has no internal midpoint. Its exterior
            # contexts already determine the output request, so calculating
            # both full-interval exits here would do unused causal work.
            frame.stage, frame.saved = 4, (chunks,)
            frames.extend(
                (
                    frame,
                    CausalFrame("output", (action, chunks[0], anchor, argument)),
                )
            )
            return True
        schedule_spatial_scan(
            workspace, frames, frame, action, 0, chunks, anchor, (chunks, argument)
        )
    elif frame.stage == 1:
        schedule_reflected_scan(workspace, frames, frame, action, values)
    elif frame.stage == 2:
        arguments = values.pop()
        arguments.reverse()
        chunks, anchors = frame.saved
        outputs = workspace.allocate(len(chunks))
        frame.stage, frame.saved = 3, (chunks,)
        frames.extend(
            (
                frame,
                CausalFrame(
                    "output_chunk_list",
                    (action, chunks, anchors, arguments, 0, outputs),
                ),
            )
        )
    else:
        outputs = values.pop()
        (chunks,) = frame.saved
        merged = None
        for index in range(len(outputs)):
            tile = outputs[len(outputs) - index - 1 if side else index]
            if side:
                tile = engine._keep(engine.tiles.mirror(tile))
            node = engine.tiles.resolve(tile)
            child = BoundaryTileView(tile, 0, node.width)
            if merged is None:
                merged, lease = child, engine.tiles.retain(tile)
            else:
                # Output content may coincide across different producing
                # requests.  Reuse its existing concat binding before walking
                # children, just as source-prefix concatenation already does.
                merged, lease = concat_cached_boundary_views(
                    engine.scheduler.results,
                    node.alphabet,
                    merged,
                    child,
                    dependencies=(
                        engine.scheduler._causal_dependencies
                        if engine._application is not None
                        else None
                    ),
                    application=engine._application,
                )
            engine._leases.append(lease)
        outputs.close()
        chunks.close()
        if merged is None:
            raise AssertionError("empty causal boundary output")
        values.append(BoundaryTileView(merged.tile, 0, view.relative_extent))
        engine.ledger.bump("tile_causal_boundary_output_completions")
    return True
