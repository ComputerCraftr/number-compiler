"""Output-free interface tasks for causal width descent."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    _attach_bound_reverse_output,
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
    CausalFrame,
    CausalPrefix,
    result_payload,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    _bind_reverse_output_request,
    causal_interface_key,
    lookup_causal_interface,
    publish_causal_interface,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    ReverseBoundOutputKey,
)
from number_compiler.hashlife.tiles.tile_reverse_bound_output_memo import (
    lookup_reverse_bound_output,
    publish_reverse_bound_output_leaf,
    publish_reverse_bound_output_parent,
)
from number_compiler.resources.causal_workspace import CausalResults
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


@dataclass(frozen=True, slots=True)
class _LeafInterface:
    symbol: int
    payload: CausalInterfacePayload


def _publish_interface(
    engine: Any,
    key: CausalInterfaceKey,
    payload: CausalInterfacePayload,
) -> CausalInterfacePayload:
    """Publish an active observation only after binding its full request."""
    if payload.bound_reverse_output is not None:
        payload = _bind_reverse_output_request(key, payload)
    return publish_causal_interface(engine.scheduler.results, key, payload)


def _primitive_parent_payload(
    engine: Any,
    action: Any,
    tile: Any,
    left: int,
    right: int,
) -> CausalInterfacePayload | None:
    """Use a certified primitive parent interface before child descent."""
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.arithmetic.radix_division import (
        certified_binary_division_radix,
    )
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    kernel = engine._law(action)
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
        engine._wiring(action),
        occurrence,
        physical_support=support,
    )


def _leaf(
    engine: Any,
    action: Any,
    left: int,
    symbol: int,
    right: int,
    require_output: bool,
) -> _LeafInterface:
    wiring = engine._wiring(action)
    output, interface, occurrence = engine.adapter.leaf_interface_symbol(
        action,
        symbol,
        (left, right),
        wiring,
    )
    action_weight = engine._cocycle(action)
    outgoing = (
        engine.adapter._observe(interface, "boundary_left", (left, right)),
        engine.adapter._observe(interface, "boundary_right", (left, right)),
    )
    active = bool(engine.adapter._observe(interface, "activity", (left, right)))
    law = engine._law(action)
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
        payload = _attach_bound_reverse_output(payload, bound_reverse_output)
    return _LeafInterface(output, payload)


def interface_step(
    engine: Any,
    frame: CausalFrame,
    frames: Any,
    values: CausalResults,
) -> bool:
    """Execute one recognized interface task; return false for other ops."""
    if frame.op == "exact_reverse_output":
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
                    CausalFrame("exact_reverse_output", (node.right,)),
                    CausalFrame("exact_reverse_output", (node.left,)),
                )
            )
        else:
            right_output, left_output = values.pop(), values.pop()
            if (
                type(left_output) is not ReverseBoundOutput
                or type(right_output) is not ReverseBoundOutput
            ):
                raise TypeError("exact reverse output children have another sort")
            values.append(
                publish_reverse_bound_output_parent(
                    engine.scheduler.results,
                    summary_key,
                    left_output,
                    right_output,
                )
            )
        return True
    if frame.op == "child_states":
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
                    CausalFrame(
                        "advance",
                        (
                            action,
                            1,
                            right,
                            BoundaryTileView(node.right, 0, child_width, 1),
                        ),
                    ),
                    CausalFrame(
                        "advance",
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
            right_mid, left_mid = values.pop(), values.pop()
            values.append(((left, right_mid), (left_mid, right)))
        return True
    if frame.op in ("interface", "reverse_interface"):
        require_output = frame.op == "reverse_interface"
        action, tile, left, right = frame.args
        node = engine.tiles.resolve(tile)
        observation_key: CausalInterfaceKey | None = None
        midpoint_missed = False
        if frame.stage == 20:
            bound_output = values.pop()
            observation_key, payload = frame.saved
            if type(bound_output) is not ReverseBoundOutput:
                raise TypeError("exact producer returned another output summary")
            if type(observation_key) is not CausalInterfaceKey:
                raise TypeError("exact producer summary lost its request")
            if type(payload) is not CausalInterfacePayload:
                raise TypeError("exact producer summary lost its interface")
            values.append(
                _publish_interface(
                    engine,
                    observation_key,
                    _attach_bound_reverse_output(payload, bound_output),
                )
            )
            engine.ledger.bump(_execution_keys.REVERSE_EXACT_OUTPUT_SUMMARY_EVALUATIONS)
            return True
        if frame.stage >= 30:
            from number_compiler.hashlife.execution.tile_causal_interface_midpoint import (
                cached_midpoint_interface_step,
            )

            children = engine._children(action)
            if children is None:
                raise AssertionError("cached interface midpoint lost its temporal edge")
            observation_key = frame.saved[-1]
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
            if engine._children(action) is None:
                if type(left) is not int or type(right) is not int:
                    raise TypeError("primitive causal interface requires finite ports")
                key, completed = probe_causal_result(
                    engine.scheduler.results,
                    action,
                    tile,
                    PrimitiveCausalPorts(left, right),
                    engine._wiring(action),
                    action_admission=engine._action_admission_token,
                )
            else:
                key = engine._composite_key(action, tile, left, right)
                completed = (
                    None
                    if key is None
                    else lookup_causal_result(
                        engine.scheduler.results,
                        key,
                        action_admission=engine._action_admission_token,
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
                if engine._application is None:
                    engine._result_leases.append(completed)
                else:
                    if key is None:
                        raise AssertionError(
                            "causal interface result lost its completed request"
                        )
                    engine.scheduler._pin_causal(
                        engine._application,
                        key,
                        completed,
                    )
                payload = interface_payload_from_causal(
                    engine.scheduler.results,
                    action,
                    causal,
                    engine._wiring(action),
                    expected_level=node.level,
                )
                if require_output:
                    if observation_key is None:
                        raise AssertionError("exact producer summary lost its request")
                    frame.stage, frame.saved = 20, (observation_key, payload)
                    frames.extend(
                        (
                            frame,
                            CausalFrame("exact_reverse_output", (causal.output,)),
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
            children = engine._children(action)
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
            if engine._children(action) is None and not require_output:
                if type(left) is not int or type(right) is not int:
                    raise TypeError("primitive causal interface requires finite ports")
                payload = _primitive_parent_payload(engine, action, tile, left, right)
                if payload is not None:
                    values.append(
                        payload
                        if observation_key is None
                        else _publish_interface(engine, observation_key, payload)
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
                        CausalFrame(
                            "interface_emit",
                            (action, left, node.symbol, right, require_output),
                        ),
                    )
                )
            else:
                leaf = values.pop()
                observation_key = frame.saved[0]
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
                    CausalFrame(
                        "child_states",
                        (action, tile, left, right),
                    ),
                )
            )
        elif frame.stage == 1:
            left_context, right_context = values.pop()
            observation_key = frame.saved[0]
            frame.stage, frame.saved = (
                2,
                (
                    observation_key,
                    left_context,
                    right_context,
                ),
            )
            frames.extend(
                (
                    frame,
                    CausalFrame(
                        frame.op,
                        (action, node.left, *left_context),
                    ),
                )
            )
        elif frame.stage == 2:
            left_payload = values.pop()
            observation_key, left_context, right_context = frame.saved
            frame.stage, frame.saved = 3, (observation_key, left_payload)
            frames.extend(
                (
                    frame,
                    CausalFrame(
                        frame.op,
                        (action, node.right, *right_context),
                    ),
                )
            )
        else:
            right_payload = values.pop()
            observation_key, left_payload = frame.saved
            payload = combine_causal_interfaces(
                engine.scheduler.results,
                action,
                left_payload,
                right_payload,
                engine._wiring(action),
                expected_level=node.level,
            )
            values.append(
                payload
                if observation_key is None
                else _publish_interface(engine, observation_key, payload)
            )
        return True
    if frame.op != "interface_emit":
        return False
    action, left, symbol, right, require_output = frame.args
    if type(require_output) is not bool:
        raise TypeError("interface output demand requires an exact Boolean")
    children = engine._children(action)
    if children is None:
        values.append(_leaf(engine, action, left, symbol, right, require_output))
        return True
    before, after = children
    match (left, right):
        case (CausalPrefix(), CausalPrefix()):
            pass
        case _:
            raise ValueError("composite interface emission requires causal prefixes")
    if frame.stage == 4:
        second, first = values.pop(), frame.saved[0]
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
            second_payload = _attach_bound_reverse_output(
                second_payload,
                second.payload.bound_reverse_output,
            )
        values.append(
            _LeafInterface(
                second.symbol,
                second_payload,
            )
        )
    elif frame.stage == 0:
        frame.stage = 1
        frames.extend(
            (
                frame,
                CausalFrame("anchor", (before, 1, right)),
                CausalFrame("anchor", (before, 0, left)),
            )
        )
    elif frame.stage == 1:
        right_anchor, left_anchor = values.pop(), values.pop()
        frame.stage, frame.saved = 2, (left_anchor, right_anchor)
        frames.extend(
            (
                frame,
                CausalFrame("advance_symbol", (before, 1, right_anchor, symbol)),
                CausalFrame("advance_symbol", (before, 0, left_anchor, symbol)),
                CausalFrame(
                    "interface_emit",
                    (before, left_anchor, symbol, right_anchor, require_output),
                ),
            )
        )
    elif frame.stage == 2:
        right_argument, left_argument, first = values.pop(), values.pop(), values.pop()
        frame.stage, frame.saved = 3, (first,)
        frames.extend(
            (
                frame,
                CausalFrame("residual", (action, 1, right, left_argument)),
                CausalFrame("residual", (action, 0, left, right_argument)),
            )
        )
    else:
        second_right, second_left = values.pop(), values.pop()
        frame.stage = 4
        frames.extend(
            (
                frame,
                CausalFrame(
                    "interface_emit",
                    (
                        after,
                        second_left,
                        frame.saved[0].symbol,
                        second_right,
                        require_output,
                    ),
                ),
            )
        )
    return True


__all__ = ["interface_step"]
