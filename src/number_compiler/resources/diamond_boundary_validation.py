"""Store-free diamond boundary validation operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
    _BaseLeftState,
    _BaseRightState,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
)
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    CellNode,
    FormalSymbolID,
    PortSignature,
    TemporalActionNode,
    _CellKey,
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
    DigitNormalizeBlockEffect,
    _DigitLeftState,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.diamond_payload import (
        DiamondPayloadRegistry,
    )


def _original_cell(
    self: DiamondPayloadRegistry, handle: CellID | FormalSymbolID
) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if type(handle) is FormalSymbolID:
        return self._handle(handle)
    for arena in self.cells:
        if handle.owner is not arena.token:
            continue
        pending = [handle.local_id]
        seen: set[int] = set()
        while pending:
            index = pending.pop()
            if index in seen:
                continue
            if not _integer(index, 0, len(arena._nodes)):
                return False
            seen.add(index)
            node = arena._nodes[index]
            if node.kind == "source":
                if not any(
                    tile.node_id == node.source_tile
                    for tile in arena.source_geometry.nodes.values()
                ):
                    return False
            elif node.kind == "join" and all(
                _integer(child, 0, len(arena._nodes))
                for child in (node.left, node.right)
            ):
                if any(
                    arena._nodes[child].level + 1 != node.level
                    for child in (node.left, node.right)
                ):
                    return False
                pending.extend((node.left, node.right))
            else:
                return False
        return True
    return False


def _boundary(self: DiamondPayloadRegistry, value: object) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if type(value) is BoundaryFunctionSignature:
        return self._function_signature(value)
    if type(value) is ImageBinding:
        return self._binding(value)
    if type(value) is ContinuationStep:
        return self._step(value)
    if type(value) is BoundaryStateNode:
        if (
            type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self._handle(value.action)
            or not _integer(value.side, 0, 2)
        ):
            return False
        if value.anchor is not None or value.continuation is not None:
            if not (
                value.literal == -1
                and type(value.literal) is int
                and type(value.anchor) is BoundaryStateID
                and type(value.continuation) is BoundaryActionID
                and self._handle(value.anchor)
                and self._handle(value.continuation)
                and value.anchor.owner is value.continuation.owner
            ):
                return False
            anchor, continuation = (
                self._state_node(value.anchor),
                self._function_node(value.continuation),
            )
            if anchor is None or continuation is None or continuation.signature is None:
                return False
            signature = continuation.signature
            for arena in self.temporal:
                if value.action.owner is arena.token:
                    node = arena._nodes[value.action.local_id]
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
            node = arena._nodes[value.action.local_id]
            if node.kind == "identity":
                return type(value.literal) is int and value.literal == 0
            if node.kind != "atom":
                return False
            effect = arena.compiler._nodes[node.compiler_id]
            for kernel_arena in self.kernels:
                for kernel in kernel_arena._kernels:
                    if kernel.effect is effect:
                        return _integer(
                            value.literal,
                            0,
                            len(kernel.left if value.side == 0 else kernel.right),
                        )
        return False
    if type(value) is ContinuationNode:
        if type(
            value.signature
        ) is not BoundaryFunctionSignature or not self._function_signature(
            value.signature
        ):
            return False
        if value.kind == "invalid":
            return value == ContinuationNode("invalid", signature=value.signature)
        if value.kind == "constant":
            if not (
                type(value.value) is BoundaryStateID
                and self._handle(value.value)
                and type(value.bit) is int
                and value.bit == -1
                and value.low is None
                and value.high is None
                and value.step is None
            ):
                return False
            state = self._state_node(value.value)
            return (
                state is not None
                and state.action == value.signature.output_action
                and state.side == value.signature.output_side
            )
        if value.kind == "decision":
            if not (
                _integer(value.bit, 0, 64)
                and value.value is None
                and value.step is None
                and type(value.low) is BoundaryActionID
                and type(value.high) is BoundaryActionID
                and self._handle(value.low)
                and self._handle(value.high)
                and value.low.owner is value.high.owner
            ):
                return False
            low, high = (
                self._function_node(value.low),
                self._function_node(value.high),
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
                and self._step(step)
                and value.signature.input_action == step.first
                and value.signature.input_side == 1 - step.side
                and value.signature.output_action == step.second
                and value.signature.output_side == step.side
            )
    return False


def _function_signature(
    self: DiamondPayloadRegistry, value: BoundaryFunctionSignature
) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if (
        type(value.input_action) is not ActionProgramID
        or type(value.output_action) is not ActionProgramID
        or value.input_action.kind != "diamond-action"
        or value.output_action.kind != "diamond-action"
        or not self._handle(value.input_action)
        or not self._handle(value.output_action)
        or value.input_action.owner is not value.output_action.owner
        or not _integer(value.input_side, 0, 2)
        or not _integer(value.output_side, 0, 2)
    ):
        return False
    for arena in self.temporal:
        if value.input_action.owner is not arena.token:
            continue
        node = arena._nodes[value.input_action.local_id]
        output = arena._nodes[value.output_action.local_id]
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
        effect = arena.compiler._nodes[node.compiler_id]
        for kernel_arena in self.kernels:
            for kernel in kernel_arena._kernels:
                if kernel.effect is effect:
                    return type(value.input_size) is int and value.input_size == len(
                        kernel.left if value.input_side == 0 else kernel.right
                    )
    return False


def _port_signature(self: DiamondPayloadRegistry, value: PortSignature) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if (
        type(value.kernel) is not ActionProgramID
        or value.kernel.kind != "diamond-kernel"
        or not self._handle(value.kernel)
        or value.first is not None
        or value.second is not None
        or value.left_role != "left-boundary"
        or value.right_role != "right-boundary"
        or not _integer(value.halo_left)
        or not _integer(value.halo_right)
        or value.horizon is not None
        and not _integer(value.horizon)
    ):
        return False
    for arena in self.kernels:
        if value.kernel.owner is arena.owner:
            kernel = arena._kernels[value.kernel.local_id]
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


def _temporal(self: DiamondPayloadRegistry, value: TemporalActionNode) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if (
        not _integer(value.left, -1)
        or not _integer(value.right, -1)
        or not _integer(value.compiler_id, -1)
        or not _integer(value.exponent)
        or not _integer(value.base)
        or not _integer(value.blank)
    ):
        return False
    if value.kind == "identity":
        return value == TemporalActionNode("identity")
    for arena in self.temporal:
        if value.kind == "atom" and value.left == value.right == -1:
            if not _integer(value.compiler_id, 0, len(arena.compiler._nodes)):
                continue
            effect = arena.compiler._nodes[value.compiler_id]
            if (value.base, value.blank, value.exponent) == (
                effect.base,
                effect.blank,
                effect.exponent,
            ):
                return True
        if value.kind == "compose" and value.compiler_id == -1:
            if not all(
                _integer(index, 0, len(arena._nodes))
                for index in (value.left, value.right)
            ):
                continue
            before, after = arena._nodes[value.left], arena._nodes[value.right]
            if (
                before.base == after.base == value.base
                and before.blank == after.blank == value.blank
                and before.exponent + after.exponent == value.exponent
            ):
                return True
    return False


def _cell(self: DiamondPayloadRegistry, value: CellNode | _CellKey) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if (
        value.kind not in ("source", "image", "slice", "join", "mirror")
        or not _integer(value.level)
        or not _integer(value.offset)
        or any(
            not _integer(index, -1)
            for index in (value.left, value.right, value.action, value.source_tile)
        )
        or isinstance(value, CellNode)
        and not _integer(value.source_start)
    ):
        return False
    for arena in self.cells:
        if isinstance(value, CellNode):
            if self._cell_owners.get(id(value)) is not arena:
                continue
            expected_original = value.kind == "source"
            if value.kind == "join":
                expected_original = (
                    _integer(value.left, 0, len(arena._nodes))
                    and _integer(value.right, 0, len(arena._nodes))
                    and arena._nodes[value.left].original_forward is True
                    and arena._nodes[value.right].original_forward is True
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
        if value.source_tile != -1 or not _integer(value.left, 0, len(arena._nodes)):
            continue
        before = arena._nodes[value.left]
        if value.kind == "image":
            if (
                value.right == -1
                and value.offset == 0
                and value.level == before.level
                and _integer(value.action, 0, len(arena.actions._nodes))
            ):
                return True
        elif value.kind == "join":
            if (
                value.action == -1
                and value.offset == 0
                and value.level == before.level + 1
                and _integer(value.right, 0, len(arena._nodes))
                and arena._nodes[value.right].level == before.level
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


def _kernel_fields(self: DiamondPayloadRegistry, value: PrimitiveKernel) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import (
        _integer,
        _physical_four,
    )

    if (
        value.ledger is not self.ledger
        or type(value.left) is not tuple
        or type(value.right) is not tuple
        or not value.left
        or not value.right
        or not any(
            any(item is value for item in arena._kernels) for arena in self.kernels
        )
    ):
        return False
    effect = value.effect
    if not _integer(effect.blank, 0, 1 << 64):
        return False
    if type(effect) is BaseBlockEffect:
        return all(
            type(state) is _BaseLeftState
            and _integer(state.carry, 0, 2)
            and _integer(state.previous_pair, -1, effect.blank + 1)
            and type(state.blank_seen) is bool
            and type(state.sink) is bool
            for state in value.left
        ) and all(
            type(state) is _BaseRightState
            and type(state.forward_suffix) is CarryFn
            and type(state.backward_suffix) is CarryFn
            for state in value.right
        )
    if type(effect) is DigitNormalizeBlockEffect:
        return all(
            type(state) is _DigitLeftState
            and _integer(state.carry, 0, 2)
            and type(state.blank_seen) is bool
            and type(state.sink) is bool
            for state in value.left
        ) and all(type(state) is int and state == 0 for state in value.right)
    if type(effect) is FiniteBlockEffect:
        return (
            all(type(state) is int for state in (*value.left, *value.right))
            and value.left == tuple(range(effect.left_count))
            and value.right == tuple(range(effect.right_count))
        )
    if type(effect) is SymbolicBinaryDivisionEffect:
        effect.__post_init__()
        return (
            value.left == (0,)
            and value.right == (0,)
            and value.left_count == 1
            and value.right_count == 2 * effect.radix
        )
    if type(effect) is CollatzPhysicalBlockEffect:
        return all(_integer(state, 0, 64) for state in (*value.left, *value.right))
    if _physical_four(effect):
        try:
            effect.validate()
        except (TypeError, ValueError):
            return False
        return value.left == tuple(range(50)) and value.right == tuple(range(90))
    if type(effect) is NonblankBlockEffect:
        return all(_integer(state, 0, 2) for state in (*value.left, *value.right))
    return False
