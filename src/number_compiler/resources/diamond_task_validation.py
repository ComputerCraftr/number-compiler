"""Store-free diamond task validation operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    FormalSymbolID,
)
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextNode,
    ContextObservation,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Evaluate,
    Initial,
    MacroTransferKey,
    Output,
    OutputFunction,
    PairSummary,
    ResetTransfer,
    SpatialSummary,
    Substitute,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionID,
    BoundaryStateID,
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_unary import (
    PrimitiveUnaryFunctions,
    UnaryComposition,
    UnaryKernelApplication,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.diamond_payload import (
        DiamondPayloadRegistry,
    )


def _context(self: DiamondPayloadRegistry, value: object) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if type(value) is UnaryKernelApplication:
        if (
            type(value.input_kernel) is not ActionProgramID
            or type(value.kernel) is not ActionProgramID
            or value.input_kernel.owner is not value.kernel.owner
            or not self._handle(value.input_kernel)
            or not self._handle(value.kernel)
            or not _integer(value.side, 0, 2)
            or not _integer(value.input_side, 0, 2)
            or value.operation not in ("advance", "emit")
            or type(value.arguments) is not tuple
        ):
            return False
        for owner in self.unary:
            if value.kernel.owner is not owner.kernels.owner:
                continue
            try:
                target = owner.kernels.kernel(value.kernel)
                domains = tuple(
                    owner.kernels.expression(argument).domain
                    for argument in value.arguments
                )
                expected = (
                    (len(target.domain(BoundarySide(value.side))), target.blank + 1)
                    if value.operation == "advance"
                    else (target.left_count, target.blank + 1, target.right_count)
                )
                source = owner.kernels.kernel(value.input_kernel)
                domain = len(source.domain(BoundarySide(value.input_side)))
                return domains == expected and self._unary_support(
                    owner, domain, value.port, value.arguments
                )
            except (TypeError, ValueError, AttributeError):
                return False
        return False
    if type(value) is UnaryComposition:
        if (
            type(value.kernel) is not ActionProgramID
            or value.kernel.kind != "diamond-kernel"
            or not self._handle(value.kernel)
            or not _integer(value.side, 0, 2)
        ):
            return False
        for unary_arena in self.unary:
            if value.kernel.owner is not unary_arena.kernels.owner:
                continue
            try:
                primitive = unary_arena.kernels.kernel(value.kernel)
                before, _ = (
                    unary_arena.kernels.expression(part)
                    for part in (value.before, value.after)
                )
                domain = len(primitive.domain(BoundarySide(value.side)))
                return before.domain == domain and self._unary_support(
                    unary_arena, domain, value.port, (value.before, value.after)
                )
            except (TypeError, ValueError, AttributeError):
                return False
        return False
    if type(value) is ContextObservation:
        if not self._handle(value.program) or not _integer(value.side, 0, 2):
            return False
        for arena in self.contexts:
            if value.program.owner is arena.token:
                try:
                    node = arena.resolve(value.program)
                    first, second = arena.interfaces(node.action)
                    definitions = (
                        arena.actions.primitive(first),
                        arena.actions.primitive(second),
                    )
                    a, b = (
                        next(
                            kernel
                            for kernel in arena.kernels._kernels
                            if kernel.effect is effect
                        )
                        for effect in definitions
                    )
                    sizes = tuple(
                        arena.kernels.expression(part).domain
                        for part in (value.left, value.right, value.incoming)
                    )
                    return sizes == (
                        a.left_count,
                        a.right_count,
                        b.left_count if value.side == 0 else b.right_count,
                    )
                except (TypeError, ValueError, StopIteration):
                    return False
        return False
    if type(value) is ContextNode:
        if not self._handle(value.action) or not _integer(value.symbol, -1, 1 << 64):
            return False
        for arena in self.contexts:
            if value.action.owner is not arena.actions.token:
                continue
            try:
                first, _ = arena.interfaces(value.action)
                if value.kind == "leaf":
                    return 0 <= value.symbol <= arena.actions.node(
                        value.action
                    ).blank and all(
                        part is None
                        for part in (
                            value.left,
                            value.right,
                            value.middle_left,
                            value.middle_right,
                        )
                    )
                if (
                    value.kind != "join"
                    or value.symbol != -1
                    or value.left is None
                    or value.right is None
                    or value.middle_left is None
                    or value.middle_right is None
                ):
                    return False
                a = next(
                    kernel
                    for kernel in arena.kernels._kernels
                    if kernel.effect is arena.actions.primitive(first)
                )
                return (
                    arena.resolve(value.left).action
                    == value.action
                    == arena.resolve(value.right).action
                    and arena.kernels.expression(value.middle_left).domain
                    == a.left_count
                    and arena.kernels.expression(value.middle_right).domain
                    == a.right_count
                )
            except (TypeError, ValueError, StopIteration):
                return False
    return False


def _unary_support(
    self: DiamondPayloadRegistry,
    arena: PrimitiveUnaryFunctions,
    domain: int,
    port: PortVariable,
    arguments: tuple[TransferSummaryID, ...],
) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if (
        type(port) is not PortVariable
        or type(port.time) is not int
        or port.time != 0
        or not _integer(port.side, 0, 2)
        or type(port.bit) is not int
        or port.bit != 0
        or type(port.role) is not str
        or port.role
        not in ("diamond-pair-left-a", "diamond-pair-right-a", "diamond-argument")
    ):
        return False
    variables = {
        PortVariable(port.time, port.side, port.role, bit)
        for bit in range((domain - 1).bit_length())
    }
    pending = [
        bit for argument in arguments for bit in arena.kernels.expression(argument).bits
    ]
    seen: set[int] = set()
    while pending:
        handle = pending.pop()
        if handle.local_id in seen:
            continue
        seen.add(handle.local_id)
        if (
            not self._handle(handle)
            or handle.owner is not arena.kernels.functions.owner
        ):
            return False
        node = arena.kernels.functions._nodes[handle.local_id]
        if node.variable is not None:
            if node.variable not in variables:
                return False
            pending.extend(
                (
                    arena.kernels.functions._handle(node.low),
                    arena.kernels.functions._handle(node.high),
                )
            )
    return True


def _task(self: DiamondPayloadRegistry, value: object) -> bool:
    from number_compiler.hashlife.execution.diamond_payload import _integer

    if type(value) is SpatialSummary:
        if (
            type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self._handle(value.action)
            or not _integer(value.side, 0, 2)
            or type(value.cell) is not CellID
            or not self._handle(value.cell)
            or not self._original_cell(value.cell)
        ):
            return False
        for spatial_arena in self.cells:
            if (
                value.cell.owner is not spatial_arena.token
                or value.action.owner is not spatial_arena.actions.token
            ):
                continue
            spatial_node = spatial_arena.actions.node(value.action)
            source = spatial_arena.source_geometry._construction.source
            return spatial_node.kind == "atom" and (
                spatial_node.base,
                spatial_node.blank,
            ) == (source.base, source.blank)
        return False
    if type(value) is ResetTransfer:
        if (
            type(value.provider) is not ImageBinding
            or not self._binding(value.provider)
            or type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self._handle(value.action)
            or type(value.side) is not int
            or value.side != 1
        ):
            return False
        for reset_arena in self.resets:
            if value.action.owner is not reset_arena.runtime.actions.token:
                continue
            proof = reset_arena.certificates.get(value.action)
            if proof is None:
                continue
            if not self._right_reset(proof) or proof.radius is None:
                return False
            if not self._source_interface(value.action, value.provider.left.owner):
                return False
            try:
                level = reset_arena.runtime.cells.input_level(value.provider.cell)
            except (TypeError, ValueError):
                return False
            return proof.radius == 0 or level >= (proof.radius - 1).bit_length()
        return False
    if type(value) is PairSummary:
        return (
            type(value.action) is ActionProgramID
            and value.action.kind == "diamond-action"
            and self._handle(value.action)
            and type(value.cell) is CellID
            and self._handle(value.cell)
            and self._original_cell(value.cell)
        )
    if type(value) is OutputFunction:
        if not all(
            type(action) is ActionProgramID
            and action.kind == "diamond-action"
            and self._handle(action)
            for action in (value.provider, value.action)
        ):
            return False
        if value.provider.owner is not value.action.owner:
            return False
        if not any(
            value.action.owner is arena.token
            and arena._nodes[value.provider.local_id].kind == "identity"
            and arena._nodes[value.action.local_id].kind in ("identity", "atom")
            for arena in self.temporal
        ):
            return False
        states = (
            value.provider_left,
            value.provider_right,
            value.left,
            value.right,
        )
        if not all(
            type(state) is BoundaryStateID and self._handle(state) for state in states
        ):
            return False
        if len({state.owner for state in states}) != 1:
            return False
        if not all(
            self._source_interface(action, states[0].owner)
            for action in (value.provider, value.action)
        ):
            return False
        for state, action, side in zip(
            states,
            (value.provider, value.provider, value.action, value.action),
            (0, 1, 0, 1),
            strict=True,
        ):
            node = self._state_node(state)
            if node is None or node.action != action or node.side != side:
                return False
        return True
    if type(value) is Output:
        return False  # Output observations are explicitly transient.
    if type(value) is Initial:
        return (
            type(value.action) is ActionProgramID
            and value.action.kind == "diamond-action"
            and self._handle(value.action)
            and _integer(value.side, 0, 2)
        )
    if type(value) is Transfer:
        return (
            type(value.provider) is ImageBinding
            and self._binding(value.provider)
            and type(value.action) is ActionProgramID
            and value.action.kind == "diamond-action"
            and self._handle(value.action)
            and _integer(value.side, 0, 2)
            and type(value.state) is BoundaryStateID
            and self._handle(value.state)
        )
    if type(value) is Substitute:
        return (
            type(value.step) is ContinuationStep
            and self._step(value.step)
            and type(value.argument) is BoundaryStateID
            and self._handle(value.argument)
        )
    if type(value) is Evaluate:
        return (
            type(value.function) is BoundaryActionID
            and self._handle(value.function)
            and type(value.argument) is BoundaryStateID
            and self._handle(value.argument)
            and value.function.owner is value.argument.owner
        )
    if type(value) is MacroTransferKey:
        return (
            type(value.before) is ActionProgramID
            and type(value.after) is ActionProgramID
            and value.before.kind == value.after.kind == "diamond-action"
            and self._handle(value.before)
            and self._handle(value.after)
            and value.before.owner is value.after.owner
            and type(value.cell) is CellID
            and self._handle(value.cell)
            and _integer(value.side, 0, 2)
        )
    return False


def _binding(self: DiamondPayloadRegistry, value: ImageBinding) -> bool:
    if not (
        type(value.action) is ActionProgramID
        and value.action.kind == "diamond-action"
        and self._handle(value.action)
        and type(value.cell) in (CellID, FormalSymbolID)
        and self._handle(value.cell)
        and type(value.left) is BoundaryStateID
        and type(value.right) is BoundaryStateID
        and self._handle(value.left)
        and self._handle(value.right)
        and value.left.owner is value.right.owner
    ):
        return False
    left, right = self._state_node(value.left), self._state_node(value.right)
    return (
        left is not None
        and right is not None
        and left.action == right.action == value.action
        and left.side == 0
        and right.side == 1
        and self._source_interface(value.action, value.left.owner)
        and any(
            value.left.owner is arena.token
            and value.action.owner is arena.temporals.token
            and value.cell.owner
            is (
                arena.cells.formal_token
                if type(value.cell) is FormalSymbolID
                else arena.cells.token
            )
            for arena in self.boundaries
        )
        and (type(value.cell) is FormalSymbolID or self._original_cell(value.cell))
    )


def _source_interface(
    self: DiamondPayloadRegistry, action: ActionProgramID, boundary_owner: ArenaToken
) -> bool:
    for arena in self.boundaries:
        if (
            boundary_owner is not arena.token
            or action.owner is not arena.temporals.token
        ):
            continue
        node = arena.temporals.node(action)
        source = arena.cells.source_geometry._construction.source
        return node.kind == "identity" or (node.base, node.blank) == (
            source.base,
            source.blank,
        )
    return False
