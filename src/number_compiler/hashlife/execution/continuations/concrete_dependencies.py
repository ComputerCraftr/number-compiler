"""Store-free concrete dependencies operations."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_directed_residual import (
    directed_children,
)
from number_compiler.hashlife.execution.continuations.concrete_emit_continuation import (
    composed_emit_tasks,
    emit_after_task,
)
from number_compiler.hashlife.execution.continuations.concrete_port_normalization import (
    ignored_initial,
    normalize_request,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    ComposedPort as _ComposedPort,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
    PortStateID,
    ResidualBindingID,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    Residual as _Residual,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    VirtualBinding as _VirtualBinding,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    VirtualInterface as _VirtualInterface,
)
from number_compiler.hashlife.execution.continuations.provider_layers import (
    ProviderLayer,
    ProviderLayerID,
)
from number_compiler.hashlife.execution.continuations.virtual_port_transfers import (
    apply_virtual_transfer,
    compose_virtual_transfers,
    virtual_transfer_leaf,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
        ConcretePortScheduler,
    )


def _run(self: ConcretePortScheduler, root: tuple[object, ...]) -> PortAtom:
    cached = self._memo.get(root)
    if cached is not None:
        self.ledger.bump("concrete_port_task_early_hits")
        return cached
    self.ledger.bump("concrete_port_task_requests")
    tasks: list[tuple[object, ...]] = [root]
    results: list[PortAtom] = []
    while tasks:
        self.ledger.bump("concrete_port_task_frames")
        frame = normalize_request(self, tasks.pop())
        tag = cast(str, frame[0])
        if tag in ("ADV", "RES"):
            hit = self._memo.get(frame)
            if hit is not None:
                self.ledger.bump("concrete_port_task_early_hits")
                results.append(hit)
                continue
        if tag == "INIT":
            action, side = cast(FieldCellActionID, frame[1]), cast(int, frame[2])
            hit = self._memo.get(frame)
            if hit is not None:
                self.ledger.bump("concrete_port_task_early_hits")
                results.append(hit)
                continue
            canonical_initial = getattr(
                self.adapter,
                "canonical_initial",
                None,
            )
            if canonical_initial is not None:
                initial = cast(
                    Callable[[FieldCellActionID, int], PortAtom | None],
                    canonical_initial,
                )(action, side)
                if initial is not None:
                    self._validate_atom(initial)
                    self._store(frame, initial)
                    results.append(initial)
                    continue
            children = self.adapter.children(action)
            if children is None:
                initial = self.adapter.primitive_initial(action, side)
                self._validate_action_state(action, side, initial)
                self._store(frame, initial)
                results.append(initial)
            else:
                tasks.append(("INIT_COMPOSED", frame, action, side))
                tasks.append(("INIT", children[0], side))
            continue
        if tag == "INIT_COMPOSED":
            anchor = results.pop()
            key, action, side = (
                cast(tuple[object, ...], frame[1]),
                cast(FieldCellActionID, frame[2]),
                cast(int, frame[3]),
            )
            residual = self._intern_residual(
                _Residual(action, side, None, None, None, anchor),
            )
            composed_initial = self._intern_port(
                _ComposedPort(action, side, anchor, residual)
            )
            self._store(key, composed_initial)
            results.append(composed_initial)
            continue
        if tag == "ADV":
            action, side, state, cell = (
                cast(FieldCellActionID, frame[1]),
                cast(int, frame[2]),
                cast(PortAtom, frame[3]),
                cast(SourceCellID, frame[4]),
            )
            layer_id = cast(ProviderLayerID | None, frame[5])
            reverse = cast(bool, frame[6])
            key = frame
            canonical_advance = getattr(
                self.adapter,
                "canonical_advance_cell",
                None,
            )
            if canonical_advance is not None:
                canonical = (
                    cast(
                        Callable[
                            [
                                FieldCellActionID,
                                int,
                                PortAtom,
                                SourceCellID,
                                bool,
                                tuple[ProviderLayer, ...],
                            ],
                            PortAtom | None,
                        ],
                        canonical_advance,
                    )(action, side, state, cell, reverse, ())
                    if layer_id is None
                    else None
                )
                if canonical is not None:
                    self._validate_atom(canonical)
                    self._store(key, canonical)
                    results.append(canonical)
                    continue
            cached_initial: PortAtom | None = self._memo.get(("INIT", action, side))
            uniform = self.sources.resolve(cell).uniform_symbol
            _base, blank = self.sources.alphabet()
            if (
                layer_id is None
                and uniform == blank
                and cached_initial is not None
                and state == cached_initial
                and self.adapter.blank_initial_is_stable(action, side)
            ):
                self._store(key, state)
                self.ledger.bump("concrete_port_blank_parent_skips")
                results.append(state)
                continue
            children = self.adapter.children(action)
            if children is not None:
                port = self.resolve_port(cast(PortStateID, state))
                if port.action != action or port.side != side:
                    raise ValueError(
                        (
                            "composed state belongs to another action port",
                            action,
                            side,
                            port.action,
                            port.side,
                        )
                    )
                if directed_children(self, action, side) is not None:
                    tasks.append(
                        (
                            "ADV_DIRECTED",
                            key,
                            action,
                            side,
                            port,
                            cell,
                            layer_id,
                            reverse,
                        )
                    )
                    tasks.append(("INIT", children[0], 0))
                else:
                    tasks.append(
                        (
                            "ADV_COMPOSED",
                            key,
                            action,
                            side,
                            port,
                            cell,
                            layer_id,
                            reverse,
                        )
                    )
                tasks.append(
                    ("ADV", children[0], side, port.anchor, cell, layer_id, reverse)
                )
                continue
            node = self.sources.resolve(cell)
            if layer_id is not None:
                if node.level:
                    first, second = self._cell_parts(cell, reverse)
                    tasks.append(
                        (
                            "ADV_AFTER_FIRST",
                            key,
                            action,
                            side,
                            second,
                            layer_id,
                            reverse,
                        )
                    )
                    tasks.append(("ADV", action, side, state, first, layer_id, reverse))
                else:
                    layer_node = self.layers.resolve(layer_id)
                    layer = layer_node.layer
                    tasks.append(("ADV_PRIMITIVE", key, action, side, state))
                    tasks.append(
                        (
                            "EMIT",
                            layer.action,
                            layer.left,
                            layer.right,
                            cell,
                            layer_node.previous,
                        )
                    )
                continue
            if node.level:
                macro_result = self.adapter.primitive_advance_cell(
                    action,
                    side,
                    cast(int, state),
                    cell,
                    reverse,
                )
                self._validate_action_state(action, side, macro_result)
                self._store(key, macro_result)
                results.append(macro_result)
            else:
                symbol = self.sources.symbol(cell)
                out = self.adapter.primitive_advance(
                    action, side, cast(int, state), symbol
                )
                self._validate_action_state(action, side, out)
                self._store(key, out)
                results.append(out)
            continue
        if tag == "ADV_AFTER_FIRST":
            middle = results.pop()
            tasks.append(("ADV_STORE", frame[1]))
            tasks.append(
                ("ADV", frame[2], frame[3], middle, frame[4], frame[5], frame[6])
            )
            continue
        if tag == "ADV_STORE":
            stored_value = results[-1]
            self._store(cast(tuple[object, ...], frame[1]), stored_value)
            continue
        if tag == "ADV_PRIMITIVE":
            emitted_symbol = results.pop()
            primitive_result = self.adapter.primitive_advance(
                cast(FieldCellActionID, frame[2]),
                cast(int, frame[3]),
                cast(int, frame[4]),
                cast(int, emitted_symbol),
            )
            self._validate_action_state(
                cast(FieldCellActionID, frame[2]),
                cast(int, frame[3]),
                primitive_result,
            )
            self._store(cast(tuple[object, ...], frame[1]), primitive_result)
            results.append(primitive_result)
            continue
        if tag == "ADV_COMPOSED":
            anchor = results.pop()
            key, action, side, port, cell, layer_id, reverse = (
                cast(tuple[object, ...], frame[1]),
                cast(FieldCellActionID, frame[2]),
                cast(int, frame[3]),
                cast(_ComposedPort, frame[4]),
                cast(SourceCellID, frame[5]),
                cast(ProviderLayerID | None, frame[6]),
                cast(bool, frame[7]),
            )
            residual = self._intern_residual(
                _Residual(action, side, port.residual, cell, layer_id, anchor, reverse),
            )
            composed_result = self._intern_port(
                _ComposedPort(action, side, anchor, residual)
            )
            self._store(key, composed_result)
            results.append(composed_result)
            continue
        if tag == "ADV_DIRECTED":
            argument, anchor = results.pop(), results.pop()
            d_key, d_action, d_side = _directed_header(frame)
            d_port = cast(_ComposedPort, frame[4])
            prior_record = self.resolve_residual(d_port.residual)
            if prior_record.constant_result is not None:
                tasks.append(
                    (
                        "ADV_DIRECTED_STORE",
                        d_key,
                        d_action,
                        d_side,
                        anchor,
                    )
                )
                tasks.append(
                    (
                        "SECOND",
                        d_action,
                        d_side,
                        prior_record.constant_result,
                        frame[5],
                        frame[6],
                        prior_record.anchor_after,
                        argument,
                        frame[7],
                    )
                )
                continue
            tasks.append(
                (
                    "ADV_DIRECTED_PRIOR",
                    d_key,
                    d_action,
                    d_side,
                    anchor,
                    frame[5],
                    frame[6],
                    argument,
                    frame[7],
                    prior_record.anchor_after,
                )
            )
            tasks.append(("RES", d_action, d_side, d_port.residual, argument))
            continue
        if tag == "ADV_DIRECTED_PRIOR":
            prior_constant = results.pop()
            tasks.append(("ADV_DIRECTED_STORE", *frame[1:5]))
            tasks.append(
                (
                    "SECOND",
                    frame[2],
                    frame[3],
                    prior_constant,
                    frame[5],
                    frame[6],
                    frame[9],
                    frame[7],
                    frame[8],
                )
            )
            continue
        if tag == "ADV_DIRECTED_STORE":
            constant = results.pop()
            d_key, d_action, d_side = _directed_header(frame)
            d_anchor = cast(PortAtom, frame[4])
            residual = self._intern_residual(
                _Residual(
                    d_action,
                    d_side,
                    None,
                    None,
                    None,
                    d_anchor,
                    False,
                    constant,
                )
            )
            directed_state = self._intern_port(
                _ComposedPort(
                    d_action,
                    d_side,
                    d_anchor,
                    residual,
                )
            )
            self._store(d_key, directed_state)
            results.append(directed_state)
            continue
        if tag == "EMIT":
            action, left, right, cell = (
                cast(FieldCellActionID, frame[1]),
                cast(PortAtom, frame[2]),
                cast(PortAtom, frame[3]),
                cast(SourceCellID, frame[4]),
            )
            layer_id = cast(ProviderLayerID | None, frame[5])
            canonical_emit = getattr(
                self.adapter,
                "canonical_emit_leaf",
                None,
            )
            if canonical_emit is not None:
                emitted = (
                    cast(
                        Callable[
                            [
                                FieldCellActionID,
                                PortAtom,
                                PortAtom,
                                SourceCellID,
                                tuple[ProviderLayer, ...],
                            ],
                            int | None,
                        ],
                        canonical_emit,
                    )(action, left, right, cell, ())
                    if layer_id is None
                    else None
                )
                if emitted is not None:
                    results.append(emitted)
                    continue
            children = self.adapter.children(action)
            if children is not None:
                lp = self.resolve_port(cast(PortStateID, left))
                rp = self.resolve_port(cast(PortStateID, right))
                before, _after = children
                tasks.append(("EMIT_COMPOSED", action, lp, rp, cell, layer_id))
                tasks.append(("ADV", before, 0, lp.anchor, cell, layer_id, False))
                tasks.append(("ADV", before, 1, rp.anchor, cell, layer_id, False))
                continue
            node = self.sources.resolve(cell)
            if node.level:
                raise ValueError("emission requires one requested source coordinate")
            if layer_id is not None:
                layer_node = self.layers.resolve(layer_id)
                layer = layer_node.layer
                tasks.append(("EMIT_PRIMITIVE", action, left, right))
                tasks.append(
                    (
                        "EMIT",
                        layer.action,
                        layer.left,
                        layer.right,
                        cell,
                        layer_node.previous,
                    )
                )
            else:
                results.append(
                    self.adapter.primitive_emit(
                        action,
                        cast(int, left),
                        self.sources.symbol(cell),
                        cast(int, right),
                    )
                )
            continue
        if tag == "EMIT_PRIMITIVE":
            emitted_symbol = results.pop()
            results.append(
                self.adapter.primitive_emit(
                    cast(FieldCellActionID, frame[1]),
                    cast(int, frame[2]),
                    cast(int, emitted_symbol),
                    cast(int, frame[3]),
                )
            )
            continue
        if tag == "EMIT_COMPOSED":
            right_arg, left_arg = results.pop(), results.pop()
            tasks.extend(
                composed_emit_tasks(
                    self,
                    frame,
                    left_arg,
                    right_arg,
                )
            )
            continue
        if tag == "EMIT_AFTER_LEFT_RES":
            second_left = results.pop()
            tasks.append(
                emit_after_task(self, frame, second_left, cast(PortAtom, frame[7]))
            )
            continue
        if tag == "EMIT_AFTER_RES":
            second_right, second_left = results.pop(), results.pop()
            tasks.append(emit_after_task(self, frame, second_left, second_right))
            continue
        if tag == "RES":
            action, side, residual_id, argument = (
                cast(FieldCellActionID, frame[1]),
                cast(int, frame[2]),
                cast(ResidualBindingID, frame[3]),
                cast(PortAtom, frame[4]),
            )
            key = frame
            residual_record = self.resolve_residual(residual_id)
            children = self.adapter.children(action)
            if children is None:
                raise ValueError("residual belongs to a primitive action")
            before, after = children
            if residual_record.constant_result is not None:
                self._validate_action_state(
                    after,
                    side,
                    residual_record.constant_result,
                )
                self._store(key, residual_record.constant_result)
                results.append(residual_record.constant_result)
                self.ledger.bump("concrete_constant_residual_hits")
                continue
            if residual_record.previous is None:
                tasks.append(("RES_STORE", key))
                tasks.append(("INIT", after, side))
                continue
            if residual_record.cell is None:
                raise AssertionError("nonconstant residual has no source cell")
            if side == 1 and ignored_initial(self, before, 0) is not None:
                tasks.append(
                    ("RES_PREVIOUS", key, action, side, residual_record, argument)
                )
                tasks.append(("RES", action, side, residual_record.previous, argument))
                self.ledger.bump("concrete_irrelevant_port_elisions")
                continue
            tasks.append(("RES_ARGUMENT", key, action, side, residual_record, argument))
            tasks.append(
                (
                    "ADV",
                    before,
                    self._opposite(side),
                    argument,
                    residual_record.cell,
                    residual_record.layer,
                    not residual_record.reverse,
                )
            )
            continue
        if tag == "RES_ARGUMENT":
            argument_before = results.pop()
            prior_record = cast(_Residual, frame[4])
            tasks.append(
                (
                    "RES_PREVIOUS",
                    frame[1],
                    frame[2],
                    frame[3],
                    prior_record,
                    frame[5],
                )
            )
            tasks.append(
                ("RES", frame[2], frame[3], prior_record.previous, argument_before)
            )
            continue
        if tag == "RES_PREVIOUS":
            value = results.pop()
            key, action, side, prior_record, argument = (
                cast(tuple[object, ...], frame[1]),
                cast(FieldCellActionID, frame[2]),
                cast(int, frame[3]),
                cast(_Residual, frame[4]),
                cast(PortAtom, frame[5]),
            )
            previous = self.resolve_residual(
                cast(ResidualBindingID, prior_record.previous)
            )
            tasks.append(("RES_STORE", key))
            tasks.append(
                (
                    "SECOND",
                    action,
                    side,
                    value,
                    prior_record.cell,
                    prior_record.layer,
                    previous.anchor_after,
                    argument,
                    prior_record.reverse,
                )
            )
            continue
        if tag == "RES_STORE":
            self._store(cast(tuple[object, ...], frame[1]), results[-1])
            continue
        if tag == "SECOND":
            action, side, incoming, cell, layer_id, anchor, argument, reverse = (
                cast(FieldCellActionID, frame[1]),
                cast(int, frame[2]),
                cast(PortAtom, frame[3]),
                cast(SourceCellID, frame[4]),
                cast(ProviderLayerID | None, frame[5]),
                cast(PortAtom, frame[6]),
                cast(PortAtom, frame[7]),
                cast(bool, frame[8]),
            )
            before, after = cast(
                tuple[FieldCellActionID, FieldCellActionID],
                self.adapter.children(action),
            )
            self._validate_action_state(after, side, incoming)
            second_key = frame
            self.ledger.bump("concrete_port_second_requests")
            second_hit = self._memo.get(second_key)
            if second_hit is not None:
                self.ledger.bump("concrete_port_task_early_hits")
                self.ledger.bump("concrete_port_second_early_hits")
                results.append(second_hit)
                continue
            if self.adapter.children(after) is None:
                if type(incoming) is not int:
                    raise AssertionError("validated primitive state is structured")
                binding = _VirtualBinding(
                    action,
                    side,
                    cell,
                    layer_id,
                    anchor,
                    argument,
                    reverse,
                )
                tasks.append(
                    (
                        "VIRTUAL_APPLY",
                        second_key,
                        binding,
                        incoming,
                    )
                )
                tasks.append(("VIRTUAL", binding))
                continue
            node = self.sources.resolve(cell)
            if not node.level:
                layer = ProviderLayer(
                    before,
                    anchor if side == 0 else argument,
                    argument if side == 0 else anchor,
                )
                tasks.append(("SECOND_STORE", second_key))
                next_layer = self.layers.intern(layer_id, layer)
                tasks.append(("ADV", after, side, incoming, cell, next_layer, reverse))
                continue
            if layer_id is not None:
                raise AssertionError("provider layers must remain source-leaf bound")
            first, second = self._cell_parts(cell, reverse)
            tasks.append(("SECOND_STORE", second_key))
            tasks.append(
                (
                    "SECOND_MIDDLE",
                    action,
                    side,
                    incoming,
                    first,
                    second,
                    anchor,
                    argument,
                    reverse,
                )
            )
            tasks.append(
                (
                    "ADV",
                    before,
                    self._opposite(side),
                    argument,
                    second,
                    None,
                    not reverse,
                )
            )
            tasks.append(("ADV", before, side, anchor, first, None, reverse))
            continue
        if tag == "VIRTUAL":
            binding = cast(_VirtualBinding, frame[1])
            interface_id = self._virtual_bindings.get(binding)
            if interface_id is not None:
                self.resolve_virtual(interface_id)
                self.ledger.bump("concrete_virtual_interface_early_hits")
                results.append(0)
                continue
            self.ledger.bump("concrete_virtual_interface_requests")
            before, after = cast(
                tuple[FieldCellActionID, FieldCellActionID],
                self.adapter.children(binding.parent),
            )
            if self.adapter.children(after) is not None:
                raise ValueError("virtual interface consumer is not primitive")
            node = self.sources.resolve(binding.cell)
            if not node.level:
                left = binding.anchor if binding.side == 0 else binding.argument
                right = binding.argument if binding.side == 0 else binding.anchor
                tasks.append(("VIRTUAL_LEAF", binding, after))
                tasks.append(
                    (
                        "EMIT",
                        before,
                        left,
                        right,
                        binding.cell,
                        binding.layer,
                    )
                )
                continue
            if binding.layer is not None:
                raise AssertionError("provider layers must remain source-leaf bound")
            first, second = self._cell_parts(
                binding.cell,
                binding.reverse,
            )
            tasks.append(
                (
                    "VIRTUAL_MIDDLE",
                    binding,
                    after,
                    first,
                    second,
                )
            )
            tasks.append(
                (
                    "ADV",
                    before,
                    self._opposite(binding.side),
                    binding.argument,
                    second,
                    None,
                    not binding.reverse,
                )
            )
            tasks.append(
                (
                    "ADV",
                    before,
                    binding.side,
                    binding.anchor,
                    first,
                    None,
                    binding.reverse,
                )
            )
            continue
        if tag == "VIRTUAL_LEAF":
            binding, consumer, symbol = (
                cast(_VirtualBinding, frame[1]),
                cast(FieldCellActionID, frame[2]),
                cast(int, results.pop()),
            )
            outputs = virtual_transfer_leaf(
                self.adapter,
                consumer,
                binding.side,
                symbol,
            )
            self._publish_virtual(
                binding,
                _VirtualInterface(consumer, binding.side, outputs),
            )
            self.ledger.bump("concrete_virtual_interface_evaluations")
            results.append(0)
            continue
        if tag == "VIRTUAL_MIDDLE":
            middle_argument, middle_anchor = results.pop(), results.pop()
            binding, consumer, first, second = (
                cast(_VirtualBinding, frame[1]),
                cast(FieldCellActionID, frame[2]),
                cast(SourceCellID, frame[3]),
                cast(SourceCellID, frame[4]),
            )
            first_binding = _VirtualBinding(
                binding.parent,
                binding.side,
                first,
                None,
                binding.anchor,
                middle_argument,
                binding.reverse,
            )
            second_binding = _VirtualBinding(
                binding.parent,
                binding.side,
                second,
                None,
                middle_anchor,
                binding.argument,
                binding.reverse,
            )
            tasks.append(
                (
                    "VIRTUAL_COMPOSE",
                    binding,
                    consumer,
                    first_binding,
                    second_binding,
                )
            )
            tasks.append(("VIRTUAL", second_binding))
            tasks.append(("VIRTUAL", first_binding))
            continue
        if tag == "VIRTUAL_COMPOSE":
            results.pop()
            results.pop()
            binding, consumer, first_binding, second_binding = (
                cast(_VirtualBinding, frame[1]),
                cast(FieldCellActionID, frame[2]),
                cast(_VirtualBinding, frame[3]),
                cast(_VirtualBinding, frame[4]),
            )
            first_id = self._virtual_bindings[first_binding]
            second_id = self._virtual_bindings[second_binding]
            first_map = self.resolve_virtual(first_id).outputs
            second_map = self.resolve_virtual(second_id).outputs
            outputs = compose_virtual_transfers(
                self.adapter,
                consumer,
                binding.side,
                first_map,
                second_map,
            )
            self._publish_virtual(
                binding,
                _VirtualInterface(consumer, binding.side, outputs),
            )
            self.ledger.bump("concrete_virtual_interface_evaluations")
            results.append(0)
            continue
        if tag == "VIRTUAL_APPLY":
            results.pop()
            key, binding, incoming = (
                cast(tuple[object, ...], frame[1]),
                cast(_VirtualBinding, frame[2]),
                cast(int, frame[3]),
            )
            interface = self.resolve_virtual(self._virtual_bindings[binding])
            result = apply_virtual_transfer(
                self.adapter,
                interface.consumer,
                interface.side,
                interface.outputs,
                incoming,
            )
            self._validate_action_state(interface.consumer, interface.side, result)
            self._store(key, result)
            results.append(result)
            continue
        if tag == "SECOND_STORE":
            self._store(cast(tuple[object, ...], frame[1]), results[-1])
            continue
        if tag == "SECOND_MIDDLE":
            middle_argument, middle_anchor = results.pop(), results.pop()
            tasks.append(
                (
                    "SECOND_RIGHT",
                    frame[1],
                    frame[2],
                    frame[5],
                    middle_anchor,
                    frame[7],
                    frame[8],
                )
            )
            tasks.append(
                (
                    "SECOND",
                    frame[1],
                    frame[2],
                    frame[3],
                    frame[4],
                    None,
                    frame[6],
                    middle_argument,
                    frame[8],
                )
            )
            continue
        if tag == "SECOND_RIGHT":
            middle = results.pop()
            tasks.append(
                (
                    "SECOND",
                    frame[1],
                    frame[2],
                    middle,
                    frame[3],
                    None,
                    frame[4],
                    frame[5],
                    frame[6],
                )
            )
            continue
        raise AssertionError(f"unknown concrete port task {tag}")
    if len(results) != 1:
        raise AssertionError((root[0], len(results)))
    self._store(root, results[0])
    return results[0]


def _directed_header(
    frame: tuple[object, ...],
) -> tuple[tuple[object, ...], FieldCellActionID, int]:
    return (
        cast(tuple[object, ...], frame[1]),
        cast(FieldCellActionID, frame[2]),
        cast(int, frame[3]),
    )
