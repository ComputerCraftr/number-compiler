"""Primitive and temporal-spatial causal emission task owner."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.causal_frames import (
    AdvanceSymbolFrame,
    AnchorFrame,
    CausalTaskFrame,
    EmitFrame,
    ResidualFrame,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    PrimitiveCausalPorts,
    primitive_causal_semantics,
    probe_causal_result,
    publish_causal_completed,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    retain_completed,
    temporal_payload,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalPrefix,
    CausalTaskValue,
    pop_causal_state,
    pop_completed_output,
)
from number_compiler.resources.metric_keys import hashlife_execution as _execution_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def emit_step(
    engine: CausalTileEngine,
    frame: EmitFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
) -> None:
    """Execute one primitive emission or one completed temporal join."""
    action, left, symbol, right = frame.args
    children = engine._children(action)
    if children is None:
        if type(left) is not int or type(right) is not int:
            raise TypeError("primitive emission requires finite boundary ports")
        alphabet = engine.adapter.alphabet(action)
        source = engine.tiles.leaf(alphabet, symbol)
        engine._leases.append(source)
        wiring = engine._wiring(action)
        key, completed = probe_causal_result(
            engine.scheduler.results,
            action,
            source.tile,
            PrimitiveCausalPorts(left, right),
            wiring,
            action_admission=engine.action_admission,
        )
        if completed is not None:
            payload = retain_completed(engine, key, completed)
            engine.ledger.bump(_execution_keys.TILE_CAUSAL_RESULT_HITS)
            values.append(payload)
            return
        output_symbol = engine._law(action).emit(left, symbol, right)
        output = engine.tiles.leaf(alphabet, output_symbol)
        engine._leases.append(output)
        interface = engine.adapter.leaf_interface(action, source.tile, wiring)
        occurrence = engine.adapter.leaf_observation(
            action,
            source.tile,
            interface,
            (left, right),
        )
        semantics = primitive_causal_semantics(
            engine.scheduler.results,
            action,
            source.tile,
            output.tile,
            PrimitiveCausalPorts(left, right),
            wiring,
            occurrence,
        )
        from number_compiler.hashlife.execution.tile_physical_support import (
            primitive_physical_support,
        )

        support = primitive_physical_support(
            engine.scheduler,
            action,
            source.tile,
            (left, right),
        )
        if support is not None:
            semantics = replace(semantics, physical_support=support)
        forward = BoundaryTileView(output.tile, 0, 1)
        backward = BoundaryTileView(output.tile, 0, 1, 1)
        payload = CausalCompletedOutput(
            output.tile,
            replace(
                semantics,
                outgoing_boundaries=BoundaryTileOperands(forward, backward),
            ),
            (left, right),
        )
        completed = publish_causal_completed(
            engine.scheduler.results,
            key,
            payload,
        )
        values.append(retain_completed(engine, key, completed))
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_PRIMITIVE_EMITS)
        return

    before, after = children
    if frame.stage == 4:
        second = pop_completed_output(values)
        match frame.saved:
            case (CausalCompletedOutput() as first,):
                pass
            case _:
                raise AssertionError("causal temporal emission lost its first result")
        match (left, right):
            case (CausalPrefix() as left_prefix, CausalPrefix() as right_prefix):
                pass
            case _:
                raise AssertionError("causal temporal emission lost its prefixes")
        values.append(
            temporal_payload(
                engine.adapter,
                before,
                after,
                first,
                second,
                left_prefix.explicit_edge or right_prefix.explicit_edge,
            )
        )
        return
    if frame.stage == 0:
        match (left, right):
            case (CausalPrefix(), CausalPrefix()):
                pass
            case _:
                raise ValueError("composite emission requires two causal prefixes")
        frame.stage = 1
        frames.extend(
            (
                frame,
                AnchorFrame((before, 1, right)),
                AnchorFrame((before, 0, left)),
            )
        )
        return
    if frame.stage == 1:
        right_anchor = pop_causal_state(values)
        left_anchor = pop_causal_state(values)
        frame.stage, frame.saved = 2, (left_anchor, right_anchor)
        frames.extend(
            (
                frame,
                AdvanceSymbolFrame((before, 1, right_anchor, symbol)),
                AdvanceSymbolFrame((before, 0, left_anchor, symbol)),
                EmitFrame((before, left_anchor, symbol, right_anchor)),
            )
        )
        return
    if frame.stage == 2:
        right_argument = pop_causal_state(values)
        left_argument = pop_causal_state(values)
        first = pop_completed_output(values)
        frame.stage, frame.saved = 3, (first,)
        frames.extend(
            (
                frame,
                ResidualFrame((action, 1, right, left_argument)),
                ResidualFrame((action, 0, left, right_argument)),
            )
        )
        return
    second_right = pop_causal_state(values)
    second_left = pop_causal_state(values)
    match frame.saved:
        case (CausalCompletedOutput() as first,):
            pass
        case _:
            raise AssertionError("causal emission lost its first result")
    first_symbol = engine.tiles.resolve(first.output).symbol
    if first_symbol is None:
        raise ValueError("causal emission midpoint has no symbol")
    frame.stage = 4
    frame.saved = (first,)
    frames.extend(
        (
            frame,
            EmitFrame((after, second_left, first_symbol, second_right)),
        )
    )


__all__ = ["emit_step"]
