"""Store-free diamond boundary validation operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    BaseLeftState,
    BaseRightState,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_integer_in_range,
    is_exact_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
)
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    CellIndexKey,
    CellNode,
    FormalSymbolID,
    PortSignature,
    TemporalActionNode,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionID,
    BoundaryFunctionSignature,
    BoundaryStateID,
    BoundaryStateNode,
    ContinuationNode,
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.projection.digit_terminal import (
    DigitLeftState,
    DigitNormalizeBlockEffect,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.diamond_payload import (
        DiamondPayloadRegistry,
    )


def original_cell(
    self: DiamondPayloadRegistry, handle: CellID | FormalSymbolID
) -> bool:
    if type(handle) is FormalSymbolID:
        return self.valid_handle(handle)
    for arena in self.cells:
        if handle.owner is not arena.token:
            continue
        nodes = arena.audit_snapshot().nodes
        pending = [handle.local_id]
        seen: set[int] = set()
        while pending:
            index = pending.pop()
            if index in seen:
                continue
            if not is_exact_integer_in_range(index, 0, len(nodes)):
                return False
            seen.add(index)
            node = nodes[index]
            if node.kind == "source":
                if not any(
                    tile.node_id == node.source_tile
                    for tile in arena.source_geometry.nodes.values()
                ):
                    return False
            elif node.kind == "join" and all(
                is_exact_integer_in_range(child, 0, len(nodes))
                for child in (node.left, node.right)
            ):
                if any(
                    nodes[child].level + 1 != node.level
                    for child in (node.left, node.right)
                ):
                    return False
                pending.extend((node.left, node.right))
            else:
                return False
        return True
    return False


def boundary_value(self: DiamondPayloadRegistry, value: object) -> bool:
    if type(value) is BoundaryFunctionSignature:
        return self.validate_function_signature(value)
    if type(value) is ImageBinding:
        return self.validate_binding(value)
    if type(value) is ContinuationStep:
        return self.validate_step(value)
    if type(value) is BoundaryStateNode:
        if (
            type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self.valid_handle(value.action)
            or not is_exact_integer_in_range(value.side, 0, 2)
        ):
            return False
        if value.anchor is not None or value.continuation is not None:
            if not (
                value.literal == -1
                and type(value.literal) is int
                and type(value.anchor) is BoundaryStateID
                and type(value.continuation) is BoundaryActionID
                and self.valid_handle(value.anchor)
                and self.valid_handle(value.continuation)
                and value.anchor.owner is value.continuation.owner
            ):
                return False
            anchor, continuation = (
                self.state_node(value.anchor),
                self.function_node(value.continuation),
            )
            if anchor is None or continuation is None or continuation.signature is None:
                return False
            signature = continuation.signature
            for arena in self.temporal:
                if value.action.owner is arena.token:
                    node = arena.audit_snapshot().nodes[value.action.local_id]
                    return (
                        node.kind == "compose"
                        and anchor.action.owner is arena.token
                        and anchor.action.local_id == node.left
                        and anchor.side == value.side
                        and signature.input_action == anchor.action
                        and signature.input_side == 1 - value.side
                        and signature.output_action.owner is arena.token
                        and signature.output_action.local_id == node.right
                        and signature.output_side == value.side
                    )
            return False
        for arena in self.temporal:
            if value.action.owner is not arena.token:
                continue
            node = arena.audit_snapshot().nodes[value.action.local_id]
            if node.kind == "identity":
                return type(value.literal) is int and value.literal == 0
            if node.kind != "atom":
                return False
            effect = arena.compiler.definition_at(node.compiler_id)
            for kernel_arena in self.kernels:
                for kernel in kernel_arena.audit_snapshot().kernels:
                    if kernel.effect is effect:
                        return is_exact_integer_in_range(
                            value.literal,
                            0,
                            len(kernel.left if value.side == 0 else kernel.right),
                        )
        return False
    if type(value) is ContinuationNode:
        if type(
            value.signature
        ) is not BoundaryFunctionSignature or not self.validate_function_signature(
            value.signature
        ):
            return False
        if value.kind == "invalid":
            return value == ContinuationNode("invalid", signature=value.signature)
        if value.kind == "constant":
            if not (
                type(value.value) is BoundaryStateID
                and self.valid_handle(value.value)
                and type(value.bit) is int
                and value.bit == -1
                and value.low is None
                and value.high is None
                and value.step is None
            ):
                return False
            state = self.state_node(value.value)
            return (
                state is not None
                and state.action == value.signature.output_action
                and state.side == value.signature.output_side
            )
        if value.kind == "decision":
            if not (
                is_exact_integer_in_range(value.bit, 0, 64)
                and value.value is None
                and value.step is None
                and type(value.low) is BoundaryActionID
                and type(value.high) is BoundaryActionID
                and self.valid_handle(value.low)
                and self.valid_handle(value.high)
                and value.low.owner is value.high.owner
            ):
                return False
            low, high = (
                self.function_node(value.low),
                self.function_node(value.high),
            )
            return (
                low is not None
                and high is not None
                and low.signature == high.signature == value.signature
            )
        if value.kind == "substitution":
            step = value.step
            return (
                value.value is None
                and value.low is None
                and value.high is None
                and type(value.bit) is int
                and value.bit == -1
                and type(step) is ContinuationStep
                and self.validate_step(step)
                and value.signature.input_action == step.first
                and value.signature.input_side == 1 - step.side
                and value.signature.output_action == step.second
                and value.signature.output_side == step.side
            )
    return False


def function_signature(
    self: DiamondPayloadRegistry, value: BoundaryFunctionSignature
) -> bool:
    if (
        type(value.input_action) is not ActionProgramID
        or type(value.output_action) is not ActionProgramID
        or value.input_action.kind != "diamond-action"
        or value.output_action.kind != "diamond-action"
        or not self.valid_handle(value.input_action)
        or not self.valid_handle(value.output_action)
        or value.input_action.owner is not value.output_action.owner
        or not is_exact_integer_in_range(value.input_side, 0, 2)
        or not is_exact_integer_in_range(value.output_side, 0, 2)
    ):
        return False
    for arena in self.temporal:
        if value.input_action.owner is not arena.token:
            continue
        action_nodes = arena.audit_snapshot().nodes
        node = action_nodes[value.input_action.local_id]
        output = action_nodes[value.output_action.local_id]
        if (
            node.kind != "identity"
            and output.kind != "identity"
            and (node.base, node.blank) != (output.base, output.blank)
        ):
            return False
        if node.kind == "compose":
            return value.input_size is None
        if node.kind == "identity":
            return type(value.input_size) is int and value.input_size == 1
        effect = arena.compiler.definition_at(node.compiler_id)
        for kernel_arena in self.kernels:
            for kernel in kernel_arena.audit_snapshot().kernels:
                if kernel.effect is effect:
                    return type(value.input_size) is int and value.input_size == len(
                        kernel.left if value.input_side == 0 else kernel.right
                    )
    return False


def port_signature(self: DiamondPayloadRegistry, value: PortSignature) -> bool:
    if (
        type(value.kernel) is not ActionProgramID
        or value.kernel.kind != "diamond-kernel"
        or not self.valid_handle(value.kernel)
        or value.first is not None
        or value.second is not None
        or value.left_role != "left-boundary"
        or value.right_role != "right-boundary"
        or not is_exact_integer_in_range(value.halo_left)
        or not is_exact_integer_in_range(value.halo_right)
        or value.horizon is not None
        and not is_exact_integer_in_range(value.horizon)
    ):
        return False
    for arena in self.kernels:
        if value.kernel.owner is arena.owner:
            kernel = arena.audit_snapshot().kernels[value.kernel.local_id]
            return all(
                type(item) is int
                for item in (
                    value.base,
                    value.alphabet_size,
                    value.left_domain,
                    value.right_domain,
                )
            ) and (
                value.base,
                value.alphabet_size,
                value.left_domain,
                value.right_domain,
            ) == (
                kernel.base,
                kernel.blank + 1,
                kernel.left_count,
                kernel.right_count,
            )
    return False


def temporal_node(self: DiamondPayloadRegistry, value: TemporalActionNode) -> bool:
    if (
        not is_exact_integer_in_range(value.left, -1)
        or not is_exact_integer_in_range(value.right, -1)
        or not is_exact_integer_in_range(value.compiler_id, -1)
        or not is_exact_integer_in_range(value.exponent)
        or not is_exact_integer_in_range(value.base)
        or not is_exact_integer_in_range(value.blank)
    ):
        return False
    if value.kind == "identity":
        return value == TemporalActionNode("identity")
    for arena in self.temporal:
        action_nodes = arena.audit_snapshot().nodes
        if value.kind == "atom" and value.left == value.right == -1:
            if not is_exact_integer_in_range(
                value.compiler_id, 0, arena.compiler.node_count
            ):
                continue
            effect = arena.compiler.definition_at(value.compiler_id)
            if (value.base, value.blank, value.exponent) == (
                effect.base,
                effect.blank,
                effect.exponent,
            ):
                return True
        if value.kind == "compose" and value.compiler_id == -1:
            if not all(
                is_exact_integer_in_range(index, 0, len(action_nodes))
                for index in (value.left, value.right)
            ):
                continue
            before, after = action_nodes[value.left], action_nodes[value.right]
            if (
                before.base == after.base == value.base
                and before.blank == after.blank == value.blank
                and before.exponent + after.exponent == value.exponent
            ):
                return True
    return False


def cell_node(self: DiamondPayloadRegistry, value: CellNode | CellIndexKey) -> bool:
    if (
        value.kind not in ("source", "image", "slice", "join", "mirror")
        or not is_exact_integer_in_range(value.level)
        or not is_exact_integer_in_range(value.offset)
        or any(
            not is_exact_integer_in_range(index, -1)
            for index in (value.left, value.right, value.action, value.source_tile)
        )
        or isinstance(value, CellNode)
        and not is_exact_integer_in_range(value.source_start)
    ):
        return False
    for arena in self.cells:
        cell_nodes = arena.audit_snapshot().nodes
        if isinstance(value, CellNode):
            if not self.owns_cell_record(value, arena):
                continue
            expected_original = value.kind == "source"
            if value.kind == "join":
                expected_original = (
                    is_exact_integer_in_range(value.left, 0, len(cell_nodes))
                    and is_exact_integer_in_range(value.right, 0, len(cell_nodes))
                    and cell_nodes[value.left].original_forward is True
                    and cell_nodes[value.right].original_forward is True
                )
            if (
                type(value.original_forward) is not bool
                or value.original_forward != expected_original
            ):
                continue
        if value.kind == "source":
            if (
                value.left == value.right == value.action == -1
                and value.offset == 0
                and any(
                    node.node_id == value.source_tile and node.level == value.level
                    for node in arena.source_geometry.nodes.values()
                )
            ):
                return True
            continue
        if value.source_tile != -1 or not is_exact_integer_in_range(
            value.left, 0, len(cell_nodes)
        ):
            continue
        before = cell_nodes[value.left]
        if value.kind == "image":
            if (
                value.right == -1
                and value.offset == 0
                and value.level == before.level
                and is_exact_integer_in_range(
                    value.action, 0, len(arena.actions.audit_snapshot().nodes)
                )
            ):
                return True
        elif value.kind == "join":
            if (
                value.action == -1
                and value.offset == 0
                and value.level == before.level + 1
                and is_exact_integer_in_range(value.right, 0, len(cell_nodes))
                and cell_nodes[value.right].level == before.level
            ):
                return True
        elif (
            value.kind == "mirror"
            and value.right == value.action == -1
            and value.level == before.level
            and value.offset == 0
        ) or (
            value.kind == "slice"
            and value.right == value.action == -1
            and value.level < before.level
            and value.offset.bit_length() <= before.level
            and value.offset % (1 << value.level) == 0
            and value.offset + (1 << value.level) <= (1 << before.level)
        ):
            return True
    return False


def kernel_fields(self: DiamondPayloadRegistry, value: PrimitiveKernel) -> bool:
    if (
        value.ledger is not self.ledger
        or not is_exact_object_tuple(value.left)
        or not is_exact_object_tuple(value.right)
        or not value.left
        or not value.right
        or not any(
            any(item is value for item in arena.audit_snapshot().kernels)
            for arena in self.kernels
        )
    ):
        return False
    left_states = value.left
    right_states = value.right
    effect = value.effect
    if not is_exact_integer_in_range(effect.blank, 0, 1 << 64):
        return False
    if type(effect) is BaseBlockEffect:
        return all(
            type(state) is BaseLeftState
            and is_exact_integer_in_range(state.carry, 0, 2)
            and is_exact_integer_in_range(state.previous_pair, -1, effect.blank + 1)
            and type(state.blank_seen) is bool
            and type(state.sink) is bool
            for state in left_states
        ) and all(
            type(state) is BaseRightState
            and type(state.forward_suffix) is CarryFn
            and type(state.backward_suffix) is CarryFn
            for state in right_states
        )
    if type(effect) is DigitNormalizeBlockEffect:
        return all(
            type(state) is DigitLeftState
            and is_exact_integer_in_range(state.carry, 0, 2)
            and type(state.blank_seen) is bool
            and type(state.sink) is bool
            for state in left_states
        ) and all(type(state) is int and state == 0 for state in right_states)
    if type(effect) is FiniteBlockEffect:
        return (
            all(type(state) is int for state in (*left_states, *right_states))
            and left_states == tuple(range(effect.left_count))
            and right_states == tuple(range(effect.right_count))
        )
    if type(effect) is SymbolicBinaryDivisionEffect:
        effect.__post_init__()
        return (
            left_states == (0,)
            and right_states == (0,)
            and value.left_count == 1
            and value.right_count == 2 * effect.radix
        )
    if type(effect) is NonblankBlockEffect:
        return all(
            is_exact_integer_in_range(state, 0, 2)
            for state in (*left_states, *right_states)
        )
    kernel_arena = next(
        (
            arena
            for arena in self.kernels
            if any(candidate is value for candidate in arena.audit_snapshot().kernels)
        ),
        None,
    )
    hooks = value.family_hooks
    if kernel_arena is None or hooks is None or kernel_arena.family_hooks is not hooks:
        return False
    owns_effect = hooks.owns_effect(effect)
    owns_compatibility = hooks.owns_compatibility(effect)
    if not (owns_effect or owns_compatibility):
        return False
    if owns_compatibility:
        try:
            hooks.validate_compatibility(effect)
        except (TypeError, ValueError, OSError):
            return False
    state_bounds = getattr(effect, "diamond_boundary_state_bounds", None)
    if callable(state_bounds):
        try:
            bounds = state_bounds()
        except (TypeError, ValueError):
            return False
        if not is_exact_object_tuple(bounds) or len(bounds) != 2:
            return False
        lower, upper = bounds
        if type(lower) is not int or type(upper) is not int or lower > upper:
            return False
        return all(
            is_exact_integer_in_range(state, lower, upper)
            for state in (*left_states, *right_states)
        )
    boundary_universe = getattr(effect, "boundary_universe", None)
    if callable(boundary_universe):
        try:
            left = boundary_universe(BoundarySide.LEFT)
            right = boundary_universe(BoundarySide.RIGHT)
        except (TypeError, ValueError, OSError):
            return False
        return (
            is_exact_object_tuple(left)
            and is_exact_object_tuple(right)
            and left_states == left
            and right_states == right
        )
    return False
