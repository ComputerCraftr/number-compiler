"""Dyadic causal boundary tasks; spatial work is allocated once per request."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    CausalTaskFrame,
    OutputBoundaryFrame,
    OutputChunkListFrame,
    OutputFrame,
    ScanChunksFrame,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    schedule_reflected_scan,
    schedule_spatial_scan,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_boundary_concat_memo import (
    concat_cached_boundary_views,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalTaskValue,
    pop_causal_state,
    pop_completed_output,
    pop_spatial_buffer,
    spatial_buffer_state_at,
    spatial_buffer_tile_at,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def probe_boundary_result(
    engine: CausalTileEngine, frame: OutputBoundaryFrame
) -> BoundaryTileView | None:
    """Reuse an already completed dyadic boundary before either sibling scan."""
    action, side, view, anchor, argument = frame.args
    pieces = engine._covered_chunks(view)
    if side:
        pieces = tuple(
            engine._keep(engine.tiles.mirror(tile)) for tile in reversed(pieces)
        )
        anchor, argument = argument, anchor
    engine.ledger.bump(
        _execution_keys.TILE_CAUSAL_BOUNDARY_OUTPUT_PIECE_NORMALIZATIONS,
        len(pieces),
    )
    if len(pieces) != 1:
        chunks = engine.scheduler._causal_workspace.allocate(len(pieces))
        for tile in pieces:
            chunks.append(tile)
        frame.saved = (chunks, anchor, argument)
        return None
    tile = pieces[0]
    key: PoweredResultKey | None
    if engine._children(action) is None:
        if type(anchor) is not int or type(argument) is not int:
            raise TypeError("primitive boundary requires finite endpoints")
        key, completed = probe_causal_result(
            engine.scheduler.results,
            action,
            tile,
            PrimitiveCausalPorts(anchor, argument),
            engine._wiring(action),
            action_admission=engine.action_admission,
        )
    else:
        key = engine._composite_key(action, tile, anchor, argument)
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
        chunks = engine.scheduler._causal_workspace.allocate(1)
        chunks.append(tile)
        frame.saved = (chunks, anchor, argument)
        return None
    if key is None:
        raise AssertionError("completed causal result has no request key")
    output = completed.output
    if engine._application is None:
        engine._result_leases.append(completed)
    else:
        engine.scheduler._pin_causal(engine._application, key, completed)
    if side:
        output = engine._keep(engine.tiles.mirror(output))
    engine.ledger.bump(_execution_keys.TILE_CAUSAL_BOUNDARY_COMPLETED_PARENT_HITS)
    return BoundaryTileView(output, 0, view.relative_extent)


def boundary_step(
    engine: CausalTileEngine,
    frame: OutputBoundaryFrame | OutputChunkListFrame | ScanChunksFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
) -> bool:
    workspace = engine.scheduler._causal_workspace
    if isinstance(frame, ScanChunksFrame):
        action, side, chunks, current, index, states = frame.args
        if frame.stage == 0:
            if index == len(chunks):
                values.append(states)
                return True
            frame.stage = 1
            tile = spatial_buffer_tile_at(
                chunks,
                len(chunks) - index - 1 if side else index,
            )
            width = engine.tiles.resolve(tile).width
            frames.extend(
                (
                    frame,
                    AdvanceFrame(
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
            nxt = pop_causal_state(values)
            states.append(nxt)
            frames.append(
                ScanChunksFrame((action, side, chunks, nxt, index + 1, states))
            )
        return True
    if isinstance(frame, OutputChunkListFrame):
        action, chunks, anchors, arguments, index, outputs = frame.args
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
                    OutputFrame(
                        (
                            action,
                            spatial_buffer_tile_at(chunks, index),
                            spatial_buffer_state_at(anchors, index),
                            spatial_buffer_state_at(arguments, index + 1),
                        ),
                    ),
                )
            )
        else:
            outputs.append(pop_completed_output(values).output)
            frames.append(
                OutputChunkListFrame(
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
    if not isinstance(frame, OutputBoundaryFrame):
        return False
    action, side, view, anchor, argument = frame.args
    if frame.stage == 4:
        completed = pop_completed_output(values)
        match frame.saved:
            case (chunks,):
                pass
            case _:
                raise AssertionError("single-tile boundary lost its chunks")
        output = completed.output
        output = engine._keep(
            engine.tiles.mirror(output) if side else engine.tiles.retain(output)
        )
        chunks.close()
        values.append(BoundaryTileView(output, 0, view.relative_extent))
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_BOUNDARY_SINGLE_TILE_OUTPUTS)
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_BOUNDARY_OUTPUT_COMPLETIONS)
        return True
    if frame.stage == 0:
        # Normalize once, not again after each child task returns.
        match frame.saved:
            case (chunks, anchor, argument):
                pass
            case _:
                raise AssertionError("boundary source chunks were not retained")
        if len(chunks) == 1:
            # One dyadic interval has no internal midpoint. Its exterior
            # contexts already determine the output request, so calculating
            # both full-interval exits here would do unused causal work.
            frame.stage, frame.saved = 4, (chunks,)
            frames.extend(
                (
                    frame,
                    OutputFrame(
                        (action, spatial_buffer_tile_at(chunks, 0), anchor, argument)
                    ),
                )
            )
            return True
        schedule_spatial_scan(workspace, frames, frame, action, 0, chunks, anchor)
    elif frame.stage == 1:
        schedule_reflected_scan(workspace, frames, frame, action, values)
    elif frame.stage == 2:
        arguments = pop_spatial_buffer(values)
        arguments.reverse()
        match frame.saved:
            case (chunks, anchors):
                pass
            case _:
                raise AssertionError("boundary reflection lost its anchors")
        outputs = workspace.allocate(len(chunks))
        frame.stage, frame.saved = 3, (chunks,)
        frames.extend(
            (
                frame,
                OutputChunkListFrame(
                    (action, chunks, anchors, arguments, 0, outputs),
                ),
            )
        )
    else:
        outputs = pop_spatial_buffer(values)
        match frame.saved:
            case (chunks,):
                pass
            case _:
                raise AssertionError("boundary output lost its source chunks")
        merged = None
        for index in range(len(outputs)):
            tile = spatial_buffer_tile_at(
                outputs,
                len(outputs) - index - 1 if side else index,
            )
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
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_BOUNDARY_OUTPUT_COMPLETIONS)
    return True
