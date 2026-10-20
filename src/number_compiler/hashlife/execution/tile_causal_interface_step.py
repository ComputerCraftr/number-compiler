"""Output-free interface tasks for causal width descent."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    AdvanceSymbolFrame,
    AnchorFrame,
    CausalTaskFrame,
    ChildStatesFrame,
    ExactReverseOutputFrame,
    InterfaceEmitFrame,
    InterfaceFrame,
    ResidualFrame,
    ReverseInterfaceFrame,
)
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    CausalLeafInterface,
    attach_bound_reverse_output,
    combine_causal_interfaces,
    interface_payload_from_causal,
    primitive_interface_payload,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    result_payload,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    bind_reverse_output_request,
    causal_interface_key,
    lookup_causal_interface,
    publish_causal_interface,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    PoweredResultKey,
    ReverseBoundOutputKey,
)
from number_compiler.hashlife.tiles.tile_reverse_bound_output_memo import (
    lookup_reverse_bound_output,
    publish_reverse_bound_output_leaf,
    publish_reverse_bound_output_parent,
)
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalPrefix,
    CausalTaskValue,
    pop_causal_state,
    pop_child_states,
    pop_interface_payload,
    pop_leaf_interface,
    pop_reverse_bound_output,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def _publish_interface(
    engine: CausalTileEngine,
    key: CausalInterfaceKey,
    payload: CausalInterfacePayload,
) -> CausalInterfacePayload:
    """Publish an active observation only after binding its full request."""
    if payload.bound_reverse_output is not None:
        payload = bind_reverse_output_request(key, payload)
    return publish_causal_interface(engine.scheduler.results, key, payload)


def _primitive_parent_payload(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    tile: TileID,
    left: int,
    right: int,
) -> CausalInterfacePayload | None:
    """Use a certified primitive parent interface before child descent."""
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.arithmetic.radix_division import (
        certified_binary_division_radix,
    )
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    kernel = engine.kernel_law(action)
    hooks = engine.adapter.family_hooks
    family_effect = hooks is not None and hooks.owns_effect(kernel.effect)
    zero_occurrence = (
        type(kernel.effect)
        in (
            BaseBlockEffect,
            DigitNormalizeBlockEffect,
        )
        or certified_binary_division_radix(kernel.effect) is not None
    )
    if not zero_occurrence and not family_effect:
        return None
    occurrence = TemporalCocycle()
    support = None
    if family_effect:
        assert hooks is not None
        occurrence, support = hooks.source_tile_observation(
            engine.scheduler, action, tile, left, right
        )
    return primitive_interface_payload(
        engine.scheduler.results,
        action,
        tile,
        PrimitiveCausalPorts(left, right),
        engine.result_wiring(action),
        occurrence,
        physical_support=support,
        action_admission=engine.action_admission,
    )


def _leaf(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    left: int,
    symbol: int,
    right: int,
    require_output: bool,
) -> CausalLeafInterface:
    wiring = engine.result_wiring(action)
    output, interface, occurrence = engine.adapter.leaf_interface_symbol(
        action,
        symbol,
        (left, right),
        wiring,
    )
    action_weight = engine.action_cocycle(action)
    outgoing = (
        engine.adapter.observe(interface, "boundary_left", (left, right)),
        engine.adapter.observe(interface, "boundary_right", (left, right)),
    )
    active = bool(engine.adapter.observe(interface, "activity", (left, right)))
    law = engine.kernel_law(action)
    support = None
    hooks = engine.adapter.family_hooks
    if hooks is not None and hooks.owns_effect(law.effect):
        support = hooks.symbol_support(engine.scheduler, action, symbol, (left, right))
    bound_reverse_output = (
        ReverseBoundOutput.leaf(law.base, output)
        if require_output and type(law.effect) is BaseBlockEffect
        else None
    )
    payload = CausalInterfacePayload(
        interface,
        (left, right),
        outgoing,
        0,
        active,
        action_weight.physical_ticks + occurrence.physical_ticks,
        action_weight.event_weight + occurrence.event_weight,
        action_weight.frame_shift + occurrence.frame_shift,
        physical_support=support,
    )
    if require_output and bound_reverse_output is not None:
        payload = attach_bound_reverse_output(payload, bound_reverse_output)
    return CausalLeafInterface(output, payload)


def interface_step(
    engine: CausalTileEngine,
    frame: CausalTaskFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
) -> bool:
    """Execute one recognized interface task; return false for other ops."""
    if isinstance(frame, ExactReverseOutputFrame):
        (tile,) = frame.args
        summary_key = ReverseBoundOutputKey(tile)
        if frame.stage == 0:
            cached = lookup_reverse_bound_output(engine.scheduler.results, summary_key)
            if cached is not None:
                values.append(cached)
                return True
        node = engine.tiles.resolve(tile)
        alphabet = engine.tiles.alphabet(node.alphabet)
        base = alphabet.radix
        if (
            type(base) is not int
            or alphabet.blank != 2 * base - 1
            or alphabet.symbol_count != 2 * base
            or alphabet.interpretation != "unsigned-radix-cell-with-explicit-blank"
        ):
            raise ValueError("exact reverse output has another tile alphabet")
        if not node.level:
            if node.symbol is None:
                raise ValueError("exact reverse output leaf omitted its symbol")
            values.append(
                publish_reverse_bound_output_leaf(engine.scheduler.results, summary_key)
            )
        elif frame.stage == 0:
            if node.left is None or node.right is None:
                raise ValueError("exact reverse output parent omitted its children")
            frame.stage = 1
            frames.extend(
                (
                    frame,
                    ExactReverseOutputFrame((node.right,)),
                    ExactReverseOutputFrame((node.left,)),
                )
            )
        else:
            right_output = pop_reverse_bound_output(values)
            left_output = pop_reverse_bound_output(values)
            values.append(
                publish_reverse_bound_output_parent(
                    engine.scheduler.results,
                    summary_key,
                    left_output,
                    right_output,
                )
            )
        return True
    if isinstance(frame, ChildStatesFrame):
        action, parent, left, right = frame.args
        node = engine.tiles.resolve(parent)
        if not node.level or node.left is None or node.right is None:
            raise ValueError("causal child states require a canonical parent")
        if frame.stage == 0:
            child_width = engine.tiles.resolve(node.left).width
            frame.stage = 1
            frames.extend(
                (
                    frame,
                    AdvanceFrame(
                        (
                            action,
                            1,
                            right,
                            BoundaryTileView(node.right, 0, child_width, 1),
                        ),
                    ),
                    AdvanceFrame(
                        (
                            action,
                            0,
                            left,
                            BoundaryTileView(node.left, 0, child_width),
                        ),
                    ),
                )
            )
        else:
            right_mid = pop_causal_state(values)
            left_mid = pop_causal_state(values)
            values.append(((left, right_mid), (left_mid, right)))
        return True
    if isinstance(frame, (InterfaceFrame, ReverseInterfaceFrame)):
        require_output = isinstance(frame, ReverseInterfaceFrame)
        action, tile, left, right = frame.args
        node = engine.tiles.resolve(tile)
        observation_key: CausalInterfaceKey | None = None
        midpoint_missed = False
        if frame.stage == 20:
            bound_output = pop_reverse_bound_output(values)
            match frame.saved:
                case (saved_observation_key, saved_payload):
                    pass
                case _:
                    raise RuntimeError("reverse interface lost its pending output")
            if type(saved_observation_key) is not CausalInterfaceKey:
                raise TypeError("exact producer summary lost its request")
            if type(saved_payload) is not CausalInterfacePayload:
                raise TypeError("exact producer summary lost its interface")
            values.append(
                _publish_interface(
                    engine,
                    saved_observation_key,
                    attach_bound_reverse_output(saved_payload, bound_output),
                )
            )
            engine.ledger.bump(_execution_keys.REVERSE_EXACT_OUTPUT_SUMMARY_EVALUATIONS)
            return True
        if frame.stage >= 30:
            from number_compiler.hashlife.execution.tile_causal_interface_midpoint import (
                cached_midpoint_interface_step,
            )

            children = engine.child_actions(action)
            if children is None:
                raise AssertionError("cached interface midpoint lost its temporal edge")
            match frame.saved:
                case (single_saved_key,):
                    if (
                        single_saved_key is not None
                        and type(single_saved_key) is not CausalInterfaceKey
                    ):
                        raise RuntimeError("cached interface midpoint lost its request")
                    observation_key = single_saved_key
                    pass
                case (_saved_parent, shifted_saved_key):
                    if (
                        shifted_saved_key is not None
                        and type(shifted_saved_key) is not CausalInterfaceKey
                    ):
                        raise RuntimeError("cached interface midpoint lost its request")
                    observation_key = shifted_saved_key
                case _:
                    raise RuntimeError("cached interface midpoint lost its request")
            if cached_midpoint_interface_step(
                engine,
                frame,
                frames,
                values,
                action,
                tile,
                left,
                right,
                children,
                observation_key,
            ):
                return True
            midpoint_missed = True
        if frame.stage == 0 and not midpoint_missed:
            key: PoweredResultKey | None
            if engine.child_actions(action) is None:
                if type(left) is not int or type(right) is not int:
                    raise TypeError("primitive causal interface requires finite ports")
                key, completed = probe_causal_result(
                    engine.scheduler.results,
                    action,
                    tile,
                    PrimitiveCausalPorts(left, right),
                    engine.result_wiring(action),
                    action_admission=engine.action_admission,
                )
            else:
                key = engine.composite_key(action, tile, left, right)
                completed = (
                    None
                    if key is None
                    else lookup_causal_result(
                        engine.scheduler.results,
                        key,
                        action_admission=engine.action_admission,
                    )
                )
            observation_key = (
                None
                if key is None
                else causal_interface_key(
                    key,
                    observation=(
                        "reverse-output-carry" if require_output else "interface"
                    ),
                )
            )
            if completed is not None:
                if require_output and observation_key is not None:
                    observed = lookup_causal_interface(
                        engine.scheduler.results,
                        observation_key,
                    )
                    if observed is not None:
                        completed.close()
                        values.append(observed)
                        engine.ledger.bump(
                            _execution_keys.TILE_CAUSAL_INTERFACE_PARENT_HITS
                        )
                        return True
                causal = result_payload(engine.tiles, completed)
                if engine.application_identity is None:
                    engine.lease_workspace.results.append(completed)
                else:
                    if key is None:
                        raise AssertionError(
                            "causal interface result lost its completed request"
                        )
                    engine.scheduler.pin_causal(
                        engine.application_identity,
                        key,
                        completed,
                    )
                payload = interface_payload_from_causal(
                    engine.scheduler.results,
                    action,
                    causal,
                    engine.result_wiring(action),
                    expected_level=node.level,
                )
                if require_output:
                    if observation_key is None:
                        raise AssertionError("exact producer summary lost its request")
                    frame.stage, frame.saved = 20, (observation_key, payload)
                    frames.extend(
                        (
                            frame,
                            ExactReverseOutputFrame((causal.output,)),
                        )
                    )
                    return True
                values.append(payload)
                engine.ledger.bump(_execution_keys.TILE_CAUSAL_INTERFACE_PARENT_HITS)
                return True
            if observation_key is not None:
                observed = lookup_causal_interface(
                    engine.scheduler.results,
                    observation_key,
                )
                if observed is not None:
                    values.append(observed)
                    engine.ledger.bump(
                        _execution_keys.TILE_CAUSAL_INTERFACE_PARENT_HITS
                    )
                    return True
            children = engine.child_actions(action)
            if children is not None and not require_output:
                from number_compiler.hashlife.execution.tile_causal_interface_midpoint import (
                    cached_midpoint_interface_step,
                )

                frame.saved = (observation_key,)
                if cached_midpoint_interface_step(
                    engine,
                    frame,
                    frames,
                    values,
                    action,
                    tile,
                    left,
                    right,
                    children,
                    observation_key,
                ):
                    return True
            if engine.child_actions(action) is None and not require_output:
                if type(left) is not int or type(right) is not int:
                    raise TypeError("primitive causal interface requires finite ports")
                primitive_parent_payload = _primitive_parent_payload(
                    engine, action, tile, left, right
                )
                if primitive_parent_payload is not None:
                    values.append(
                        primitive_parent_payload
                        if observation_key is None
                        else _publish_interface(
                            engine, observation_key, primitive_parent_payload
                        )
                    )
                    engine.ledger.bump(
                        _execution_keys.TILE_CAUSAL_INTERFACE_PRIMITIVE_PARENT_SHORTCUTS
                    )
                    return True
            frame.saved = (observation_key,)
        if not node.level:
            if node.symbol is None:
                raise ValueError("malformed causal interface leaf")
            if frame.stage == 0:
                frame.stage = 1
                frames.extend(
                    (
                        frame,
                        InterfaceEmitFrame(
                            (action, left, node.symbol, right, require_output),
                        ),
                    )
                )
            else:
                leaf = pop_leaf_interface(values)
                match frame.saved:
                    case (observation_key,):
                        pass
                    case _:
                        raise RuntimeError("causal interface leaf lost its request")
                values.append(
                    leaf.payload
                    if observation_key is None
                    else _publish_interface(engine, observation_key, leaf.payload)
                )
            return True
        if node.left is None or node.right is None:
            raise ValueError("malformed causal interface parent")
        if frame.stage == 0:
            frame.stage = 1
            frames.extend(
                (
                    frame,
                    ChildStatesFrame(
                        (action, tile, left, right),
                    ),
                )
            )
        elif frame.stage == 1:
            left_context, right_context = pop_child_states(values)
            match frame.saved:
                case (initial_saved_key,):
                    observation_key = initial_saved_key
                case _:
                    raise RuntimeError("causal interface lost its observation key")
            frame.stage, frame.saved = (
                2,
                (
                    observation_key,
                    left_context,
                    right_context,
                ),
            )
            child = (
                ReverseInterfaceFrame((action, node.left, *left_context))
                if require_output
                else InterfaceFrame((action, node.left, *left_context))
            )
            frames.extend((frame, child))
        elif frame.stage == 2:
            left_payload = pop_interface_payload(values)
            match frame.saved:
                case (child_saved_key, child_saved_left, child_saved_right):
                    if (
                        child_saved_key is not None
                        and type(child_saved_key) is not CausalInterfaceKey
                    ):
                        raise RuntimeError("causal interface lost its observation key")
                    observation_key = child_saved_key
                    left_context = child_saved_left
                    right_context = child_saved_right
                case _:
                    raise RuntimeError("causal interface lost its child contexts")
            frame.stage, frame.saved = 3, (observation_key, left_payload)
            child = (
                ReverseInterfaceFrame((action, node.right, *right_context))
                if require_output
                else InterfaceFrame((action, node.right, *right_context))
            )
            frames.extend((frame, child))
        else:
            right_payload = pop_interface_payload(values)
            match frame.saved:
                case (final_saved_key, final_saved_payload):
                    if (
                        final_saved_key is not None
                        and type(final_saved_key) is not CausalInterfaceKey
                    ):
                        raise RuntimeError("causal interface lost its observation key")
                    if type(final_saved_payload) is not CausalInterfacePayload:
                        raise RuntimeError("causal interface lost its left child")
                    observation_key = final_saved_key
                    left_payload = final_saved_payload
                case _:
                    raise RuntimeError("causal interface lost its left child")
            payload = combine_causal_interfaces(
                engine.scheduler.results,
                action,
                left_payload,
                right_payload,
                engine.result_wiring(action),
                expected_level=node.level,
            )
            values.append(
                payload
                if observation_key is None
                else _publish_interface(engine, observation_key, payload)
            )
        return True
    if not isinstance(frame, InterfaceEmitFrame):
        return False
    action, left, symbol, right, require_output = frame.args
    if type(require_output) is not bool:
        raise TypeError("interface output demand requires an exact Boolean")
    children = engine.child_actions(action)
    if children is None:
        if type(left) is not int or type(right) is not int:
            raise TypeError("primitive interface emission requires finite ports")
        values.append(_leaf(engine, action, left, symbol, right, require_output))
        return True
    before, after = children
    match (left, right):
        case (CausalPrefix(), CausalPrefix()):
            pass
        case _:
            raise ValueError("composite interface emission requires causal prefixes")
    if frame.stage == 4:
        second = pop_leaf_interface(values)
        match frame.saved:
            case (CausalLeafInterface() as first,):
                pass
            case _:
                raise RuntimeError("interface emission lost its first temporal result")
        from number_compiler.hashlife.execution.tile_physical_support import (
            temporal_physical_support,
        )

        second_payload = CausalInterfacePayload(
            second.payload.interface,
            second.payload.incoming_ports,
            second.payload.outgoing_ports,
            second.payload.level,
            second.payload.active,
            first.payload.physical_ticks + second.payload.physical_ticks,
            first.payload.event_weight + second.payload.event_weight,
            first.payload.frame_shift + second.payload.frame_shift,
            physical_support=temporal_physical_support(
                first.payload.physical_support,
                second.payload.physical_support,
                before_ticks=first.payload.physical_ticks,
                after_ticks=second.payload.physical_ticks,
            ),
        )
        if second.payload.bound_reverse_output is not None:
            second_payload = attach_bound_reverse_output(
                second_payload,
                second.payload.bound_reverse_output,
            )
        values.append(
            CausalLeafInterface(
                second.symbol,
                second_payload,
            )
        )
    elif frame.stage == 0:
        frame.stage = 1
        frames.extend(
            (
                frame,
                AnchorFrame((before, 1, right)),
                AnchorFrame((before, 0, left)),
            )
        )
    elif frame.stage == 1:
        right_anchor = pop_causal_state(values)
        left_anchor = pop_causal_state(values)
        frame.stage, frame.saved = 2, (left_anchor, right_anchor)
        frames.extend(
            (
                frame,
                AdvanceSymbolFrame((before, 1, right_anchor, symbol)),
                AdvanceSymbolFrame((before, 0, left_anchor, symbol)),
                InterfaceEmitFrame(
                    (before, left_anchor, symbol, right_anchor, require_output),
                ),
            )
        )
    elif frame.stage == 2:
        right_argument = pop_causal_state(values)
        left_argument = pop_causal_state(values)
        first = pop_leaf_interface(values)
        frame.stage, frame.saved = 3, (first,)
        frames.extend(
            (
                frame,
                ResidualFrame((action, 1, right, left_argument)),
                ResidualFrame((action, 0, left, right_argument)),
            )
        )
    else:
        second_right = pop_causal_state(values)
        second_left = pop_causal_state(values)
        frame.stage = 4
        match frame.saved:
            case (CausalLeafInterface() as first,):
                first_symbol = first.symbol
            case _:
                raise RuntimeError("interface emission lost its first result")
        frames.extend(
            (
                frame,
                InterfaceEmitFrame(
                    (
                        after,
                        second_left,
                        first_symbol,
                        second_right,
                        require_output,
                    ),
                ),
            )
        )
    return True


__all__ = ["interface_step"]
