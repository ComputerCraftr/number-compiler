"""Independent domains for retained diamond records and scoped references."""

from __future__ import annotations

from typing import TYPE_CHECKING, TypeGuard

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import (
    BoundedCellAction,
    CellID,
    CellNode,
    FormalSymbolID,
    ImageCellArena,
    PortProgramID,
    PortSignature,
    PortSignatureID,
    TemporalActionArena,
    TemporalActionNode,
    _CellKey,
)
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextNode,
    ContextObservation,
    ContextProgramArena,
    ContextProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_payload import (
    ExpressionPayloadRegistry,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_payload import (
    HigherPayloadRegistry,
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
from number_compiler.hashlife.execution.diamond_certificate import (
    DiamondCompositionCertificate,
)
from number_compiler.hashlife.execution.diamond_continuation_payload import (
    ContinuationPayloadRegistry,
)
from number_compiler.hashlife.execution.diamond_cycles import PhysicalCycleProjection
from number_compiler.hashlife.execution.diamond_demand_payload import (
    DemandPayloadRegistry,
)
from number_compiler.hashlife.execution.diamond_pair_macros import (
    PairMacroKey,
    PairMacroRecord,
    PrimitivePairMacros,
)
from number_compiler.hashlife.execution.diamond_primitive_pair import PrimitivePairKey
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryActionID,
    BoundaryFunctionSignature,
    BoundaryStateID,
    BoundaryStateNode,
    ContinuationNode,
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.interfaces.diamond_halos import CausalHaloArena, RightHalo
from number_compiler.hashlife.interfaces.diamond_interface_payload import (
    InterfacePayloadRegistry,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    FiniteExpression,
    PrimitiveKernel,
    _KernelApplication,
    _KernelTemplate,
    _KernelTemplateKey,
)
from number_compiler.hashlife.interfaces.diamond_resets import (
    RightResetCertificate,
    RightResetCertificates,
)
from number_compiler.hashlife.interfaces.diamond_unary import (
    PrimitiveUnaryFunctions,
    UnaryComposition,
    UnaryKernelApplication,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
        PhysicalCollatzFourBlockEffect,
    )


def _integer(value: object, lower: int = 0, upper: int | None = None) -> bool:
    return type(value) is int and value >= lower and (upper is None or value < upper)


def _physical_four(value: object) -> TypeGuard[PhysicalCollatzFourBlockEffect]:
    """Recognize an explicitly retained proof C4 atom without eager import."""
    if type(value).__name__ != "PhysicalCollatzFourBlockEffect":
        return False
    from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    return type(value) is PhysicalCollatzFourBlockEffect


class DiamondPayloadRegistry:
    """Inspect actual arena roots; roles and familiar field names grant no trust.

    This object is transient audit workspace. It does not evaluate kernels or
    observe source symbols, so collecting metrics cannot add execution work.
    """

    record_types = (
        PrimitiveKernel,
        FiniteExpression,
        _KernelApplication,
        _KernelTemplate,
        _KernelTemplateKey,
        TemporalActionNode,
        CellNode,
        _CellKey,
        PortSignature,
        BoundedCellAction,
        CellID,
        FormalSymbolID,
        PortProgramID,
        PortSignatureID,
        BoundaryActionID,
        BoundaryStateID,
        BoundaryStateNode,
        BoundaryFunctionSignature,
        ContinuationNode,
        ContinuationStep,
        ImageBinding,
        Initial,
        Transfer,
        ResetTransfer,
        Substitute,
        Evaluate,
        Output,
        OutputFunction,
        MacroTransferKey,
        PairSummary,
        SpatialSummary,
        PrimitivePairKey,
        DiamondCompositionCertificate,
        PairMacroKey,
        PairMacroRecord,
        RightHalo,
        PhysicalCycleProjection,
        ContextProgramID,
        ContextNode,
        ContextObservation,
        UnaryComposition,
        UnaryKernelApplication,
        RightResetCertificate,
        *ExpressionPayloadRegistry.record_types,
        *HigherPayloadRegistry.record_types,
        *DemandPayloadRegistry.record_types,
        *ContinuationPayloadRegistry.record_types,
        *InterfacePayloadRegistry.record_types,
    )

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        actual = dict(ledger.iter_containers())
        roots = tuple(ledger.iter_execution_roots())
        self.kernels = tuple(
            root
            for root in roots
            if type(root) is DiamondKernelArena
            and root.ledger is ledger
            and actual.get(root._kernel_owner) is root._kernels
            and actual.get(root._expression_owner) is root._expressions
        )
        self.temporal = tuple(
            root
            for root in roots
            if type(root) is TemporalActionArena
            and root.ledger is ledger
            and actual.get(root._node_owner) is root._nodes
        )
        self.cells = tuple(
            root
            for root in roots
            if type(root) is ImageCellArena
            and root.ledger is ledger
            and actual.get(root._node_owner) is root._nodes
        )
        self._cell_owners = {
            id(node): arena for arena in self.cells for node in arena._nodes
        }
        self.boundaries = tuple(
            root
            for root in roots
            if type(root) is BoundaryActionArena
            and root.ledger is ledger
            and actual.get(root.state_owner) is root.states
            and actual.get(root.action_owner) is root.actions
        )
        self.pair_macros = tuple(
            root
            for root in roots
            if type(root) is PrimitivePairMacros
            and root.ledger is ledger
            and actual.get(root._node_owner) is root._nodes
        )
        self.halos = tuple(
            root
            for root in roots
            if type(root) is CausalHaloArena
            and root.ledger is ledger
            and actual.get(root.owner) is root._radii._data
        )
        self.resets = tuple(
            root
            for root in roots
            if type(root) is RightResetCertificates
            and root.ledger is ledger
            and actual.get(root.certificates.owner) is root.certificates._data
        )
        self.contexts = tuple(
            root
            for root in roots
            if type(root) is ContextProgramArena
            and root.ledger is ledger
            and actual.get(root.node_owner) is root._nodes
        )
        self.unary = tuple(
            root
            for root in roots
            if type(root) is PrimitiveUnaryFunctions
            and root.ledger is ledger
            and actual.get(root.owner) is root._memo._data
        )
        self.domain_ids = {
            id(domain): kernel
            for arena in self.kernels
            for kernel in arena._kernels
            for domain in (kernel.left, kernel.right)
            if any(container is domain for container in actual.values())
        }
        self._kernel_checks: dict[int, bool] = {}
        from number_compiler.hashlife.observation.diamond_query import (
            DiamondApplication,
        )

        self.applications = tuple(
            root
            for root in roots
            if type(root) is DiamondApplication
            and root.ledger is ledger
            and any(container is root._certificates for container in actual.values())
        )
        self.cycle_records = {
            id(record)
            for application in self.applications
            if any(container is application._cycles for container in actual.values())
            for record in application._cycles
        }

        self.expressions = ExpressionPayloadRegistry(ledger, self._handle, self._handle)
        self.higher = HigherPayloadRegistry(ledger, self.expressions, self._handle)
        self.demands = DemandPayloadRegistry(ledger, self.kernels)
        self.continuations = ContinuationPayloadRegistry(ledger, self.expressions)
        self.interfaces = InterfacePayloadRegistry(ledger, self.expressions)

    def recognizes(self, value: object) -> bool:
        return (
            type(value) in self.record_types
            or isinstance(value, ArenaHandle)
            and value.kind.startswith("diamond-")
        )

    def _handle(self, value: object) -> bool:
        if not isinstance(value, ArenaHandle) or not _integer(value.local_id):
            return False
        if type(value) is ExprID:
            return self.expressions.handle(value)
        if type(value) is ActionProgramID:
            if value.kind == "diamond-action":
                return any(
                    value.owner is arena.token and value.local_id < len(arena._nodes)
                    for arena in self.temporal
                )
            if value.kind == "diamond-kernel":
                return any(
                    value.owner is arena.owner and value.local_id < len(arena._kernels)
                    for arena in self.kernels
                )
        if type(value) is CellID and value.kind == "diamond-cell":
            return any(
                value.owner is arena.token and value.local_id < len(arena._nodes)
                for arena in self.cells
            )
        if type(value) is FormalSymbolID and value.kind == "diamond-formal-symbol":
            return any(
                value.owner is arena.formal_token
                and value.local_id
                <= arena.source_geometry._construction.source.blank
                < (1 << 64)
                for arena in self.cells
            )
        if type(value) is BoundaryStateID and value.kind == "diamond-boundary-state":
            return any(
                value.owner is arena.token and value.local_id < len(arena.states)
                for arena in self.boundaries
            )
        if type(value) is BoundaryActionID and value.kind == "diamond-boundary-action":
            return any(
                value.owner is arena.token and value.local_id < len(arena.actions)
                for arena in self.boundaries
            )
        if type(value) is ContextProgramID and value.kind == "diamond-context-program":
            return any(
                value.owner is arena.token and value.local_id < len(arena._nodes)
                for arena in self.contexts
            )
        if type(value) is TransferSummaryID:
            if value.kind in ("diamond-higher-context", "diamond-higher-unary"):
                return self.higher.handle(value)
            if value.kind == "diamond-pair-macro":
                return any(
                    value.owner is arena.token and value.local_id < len(arena._nodes)
                    for arena in self.pair_macros
                )
            if value.kind == "diamond-finite-expression":
                return any(
                    value.owner is arena.owner
                    and value.local_id < len(arena._expressions)
                    for arena in self.kernels
                )
            if value.kind == "finite-port-function":
                return any(
                    value.owner is arena.functions.owner
                    and value.local_id < len(arena.functions._nodes)
                    for arena in self.kernels
                )
        return False

    def domain(self, value: object) -> bool:
        """Only the actual original primitive domain tuple is a semantic root."""
        kernel = self.domain_ids.get(id(value))
        return kernel is not None and self._kernel(kernel)

    def _kernel(self, value: PrimitiveKernel) -> bool:
        found = self._kernel_checks.get(id(value))
        if found is not None:
            return found
        valid = self._kernel_fields(value)
        from number_compiler.arithmetic.radix_division import (
            SymbolicBinaryDivisionEffect,
        )

        if valid and type(value.effect) is not SymbolicBinaryDivisionEffect:
            valid = value.left == value.effect.boundary_universe(
                BoundarySide.LEFT
            ) and value.right == value.effect.boundary_universe(BoundarySide.RIGHT)
        self._kernel_checks[id(value)] = valid
        return valid

    def _kernel_fields(self, value: PrimitiveKernel) -> bool:
        from number_compiler.resources.diamond_boundary_validation import _kernel_fields

        return _kernel_fields(self, value)

    def valid(self, value: object) -> bool:
        if type(value) in InterfacePayloadRegistry.record_types:
            return self.interfaces.valid(value)
        if type(value) in ContinuationPayloadRegistry.record_types:
            return self.continuations.valid(value)
        if type(value) in DemandPayloadRegistry.record_types:
            return self.demands.valid(value)
        if type(value) in HigherPayloadRegistry.record_types:
            return self.higher.valid(value)
        if type(value) in ExpressionPayloadRegistry.record_types:
            return self.expressions.valid(value)
        if isinstance(value, ArenaHandle):
            return self._handle(value)
        if type(value) is PrimitiveKernel:
            return self._kernel(value)
        if type(value) is RightHalo:
            return self._halo(value)
        if type(value) is RightResetCertificate:
            return self._right_reset(value)
        if type(value) is PhysicalCycleProjection:
            return self._physical_cycle(value)
        if type(value) is DiamondCompositionCertificate:
            if (
                type(value.kernels) is not tuple
                or type(value.law) is not str
                or value.law != "bimachine-two-sided-substitution-v1"
                or type(value.root) is not ActionProgramID
                or not self._handle(value.root)
            ):
                return False
            for pair in value.kernels:
                if (
                    type(pair) is not tuple
                    or len(pair) != 2
                    or type(pair[0]) is not ActionProgramID
                    or pair[0].kind != "diamond-action"
                    or type(pair[1]) is not ActionProgramID
                    or pair[1].kind != "diamond-kernel"
                    or not self._handle(pair[0])
                    or not self._handle(pair[1])
                ):
                    return False
            try:
                return any(
                    any(record is value for record in application._certificates)
                    and value.validate(application.runtime, application.root)
                    for application in self.applications
                )
            except (TypeError, ValueError, IndexError):
                return False
        if type(value) is FiniteExpression:
            return (
                _integer(value.domain, 1, (1 << 64) + 1)
                and type(value.bits) is tuple
                and len(value.bits) == (value.domain - 1).bit_length()
                and all(
                    type(bit) is TransferSummaryID
                    and bit.kind == "finite-port-function"
                    and self._handle(bit)
                    for bit in value.bits
                )
                and len({bit.owner for bit in value.bits}) <= 1
            )
        if type(value) is _KernelApplication:
            return (
                type(value.kernel) is ActionProgramID
                and value.kernel.kind == "diamond-kernel"
                and self._handle(value.kernel)
                and value.operation in ("advance", "emit")
                and _integer(value.side, 0, 2)
                and type(value.arguments) is tuple
                and len(value.arguments) == (2 if value.operation == "advance" else 3)
                and all(
                    type(item) is TransferSummaryID
                    and item.kind == "diamond-finite-expression"
                    and item.owner is value.kernel.owner
                    and self._handle(item)
                    for item in value.arguments
                )
            )
        if type(value) is _KernelTemplateKey:
            if not (
                type(value.kernel) is ActionProgramID
                and value.kernel.kind == "diamond-kernel"
                and self._handle(value.kernel)
                and value.operation in ("advance", "emit")
                and _integer(value.side, 0, 2)
                and type(value.constants) is tuple
            ):
                return False
            arena = next(
                arena for arena in self.kernels if arena.owner is value.kernel.owner
            )
            primitive = arena._kernels[value.kernel.local_id]
            domains = (
                (
                    len(primitive.left if value.side == 0 else primitive.right),
                    primitive.blank + 1,
                )
                if value.operation == "advance"
                else (primitive.left_count, primitive.blank + 1, primitive.right_count)
            )
            return len(value.constants) == len(domains) and all(
                item is None or _integer(item, 0, domain)
                for item, domain in zip(value.constants, domains, strict=True)
            )
        if type(value) is _KernelTemplate:
            return (
                type(value.function) is TransferSummaryID
                and value.function.kind == "diamond-finite-expression"
                and self._handle(value.function)
                and type(value.parameters) is tuple
                and len(value.parameters) in (2, 3)
                and all(
                    type(item) is TransferSummaryID
                    and item.kind == "diamond-finite-expression"
                    and item.owner is value.function.owner
                    and self._handle(item)
                    for item in value.parameters
                )
            )
        if type(value) is TemporalActionNode:
            return self._temporal(value)
        if type(value) in (CellNode, _CellKey) and isinstance(
            value, (CellNode, _CellKey)
        ):
            return self._cell(value)
        if type(value) in (
            BoundaryStateNode,
            BoundaryFunctionSignature,
            ContinuationNode,
            ContinuationStep,
            ImageBinding,
        ):
            return self._boundary(value)
        if type(value) is PortSignature:
            return self._port_signature(value)
        if type(value) in (
            Initial,
            Transfer,
            ResetTransfer,
            Substitute,
            Evaluate,
            Output,
            OutputFunction,
            MacroTransferKey,
            PairSummary,
            SpatialSummary,
        ):
            return self._task(value)
        if type(value) is PrimitivePairKey:
            if (
                type(value.action) is not ActionProgramID
                or value.action.kind != "diamond-action"
                or not self._handle(value.action)
                or type(value.state) is not BoundaryStateID
                or not self._handle(value.state)
                or not _integer(value.side, 0, 2)
            ):
                return False
            state = self._state_node(value.state)
            return (
                state is not None
                and state.action == value.action
                and state.side == value.side
                and any(
                    value.action.owner is arena.token
                    and _integer(
                        value.symbol, 0, arena._nodes[value.action.local_id].blank + 1
                    )
                    for arena in self.temporal
                )
            )
        if type(value) is PairMacroKey:
            return (
                type(value.action) is ActionProgramID
                and value.action.kind == "diamond-action"
                and self._handle(value.action)
                and type(value.cell) is CellID
                and self._handle(value.cell)
                and self._original_cell(value.cell)
            )
        if type(value) is PairMacroRecord:
            return self._pair_macro(value)
        if type(value) in (
            ContextNode,
            ContextObservation,
            UnaryComposition,
            UnaryKernelApplication,
        ):
            return self._context(value)
        # Port records become admissible only when their executable arenas are
        # available for owner membership checks. Unbound declarations fail.
        return False

    def _pair_macro(self, value: PairMacroRecord) -> bool:
        if (
            type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self._handle(value.action)
        ):
            return False
        functions = (value.left_transfer, value.right_transfer)
        if not all(
            type(function) is TransferSummaryID
            and function.kind == "diamond-finite-expression"
            and function.owner is functions[0].owner
            and self._handle(function)
            for function in functions
        ):
            return False
        for temporal in self.temporal:
            if value.action.owner is not temporal.token:
                continue
            node = temporal._nodes[value.action.local_id]
            if node.kind != "compose":
                return False
            children = temporal._nodes[node.left], temporal._nodes[node.right]
            if any(child.kind != "atom" for child in children):
                return False
            definitions = tuple(
                temporal.compiler._nodes[child.compiler_id] for child in children
            )
            for kernel_arena in self.kernels:
                if functions[0].owner is not kernel_arena.owner:
                    continue
                first = next(
                    (
                        kernel
                        for kernel in kernel_arena._kernels
                        if kernel.effect is definitions[0]
                    ),
                    None,
                )
                second = next(
                    (
                        kernel
                        for kernel in kernel_arena._kernels
                        if kernel.effect is definitions[1]
                    ),
                    None,
                )
                if first is None or second is None:
                    return False
                domains = (first.left_count, first.right_count)
                return all(
                    kernel_arena._expressions[function.local_id].domain == domain
                    for function, domain in zip(functions, domains, strict=True)
                ) and all(
                    type(context) is ContextProgramID
                    and self._handle(context)
                    and any(
                        context.owner is arena.token
                        and arena.kernels is kernel_arena
                        and arena._nodes[context.local_id].action == value.action
                        for arena in self.contexts
                    )
                    for context in (value.left_context, value.right_context)
                )
        return False

    def _context(self, value: object) -> bool:
        from number_compiler.resources.diamond_task_validation import _context

        return _context(self, value)

    def _unary_support(
        self,
        arena: PrimitiveUnaryFunctions,
        domain: int,
        port: PortVariable,
        arguments: tuple[TransferSummaryID, ...],
    ) -> bool:
        from number_compiler.resources.diamond_task_validation import _unary_support

        return _unary_support(self, arena, domain, port, arguments)

    def _task(self, value: object) -> bool:
        from number_compiler.resources.diamond_task_validation import _task

        return _task(self, value)

    def _binding(self, value: ImageBinding) -> bool:
        from number_compiler.resources.diamond_task_validation import _binding

        return _binding(self, value)

    def _source_interface(
        self, action: ActionProgramID, boundary_owner: ArenaToken
    ) -> bool:
        from number_compiler.resources.diamond_task_validation import _source_interface

        return _source_interface(self, action, boundary_owner)

    def _halo(self, value: RightHalo) -> bool:
        if (
            type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self._handle(value.action)
            or value.radius is not None
            and not _integer(value.radius)
        ):
            return False
        for arena in self.halos:
            actions = arena.runtime.actions
            if (
                value.action.owner is not actions.token
                or arena._radii.get(value.action) is not value
            ):
                continue
            node = actions.node(value.action)
            if node.kind == "identity":
                return value.radius == 0
            if node.kind == "atom":
                effect = arena.runtime.actions.primitive(value.action)
                if _physical_four(effect):
                    return value.radius == 4
                return value.radius in (None, 0, 1)
            first = arena._radii.get(actions.reference(node.first))
            second = arena._radii.get(actions.reference(node.second))
            if first is None or second is None:
                return False
            if first.radius is None or second.radius is None:
                return value.radius is None
            return (
                _integer(first.radius)
                and _integer(second.radius)
                and value.radius == first.radius + second.radius
            )
        return False

    def _right_reset(self, value: RightResetCertificate) -> bool:
        if (
            type(value.action) is not ActionProgramID
            or value.action.kind != "diamond-action"
            or not self._handle(value.action)
            or value.law != "complete-right-boundary-synchronization-v1"
            or type(value.law) is not str
            or value.radius is not None
            and not _integer(value.radius)
        ):
            return False
        for arena in self.resets:
            if (
                value.action.owner is not arena.runtime.actions.token
                or arena.certificates.get(value.action) is not value
            ):
                continue
            actions = arena.runtime.actions
            node = actions.node(value.action)
            if node.kind == "identity":
                return value.radius == 0
            if node.kind == "compose":
                left = arena.certificates.get(actions.reference(node.first))
                right = arena.certificates.get(actions.reference(node.second))
                if left is None or right is None:
                    return False
                return (
                    value.radius is None
                    if left.radius is None or right.radius is None
                    else _integer(left.radius)
                    and _integer(right.radius)
                    and value.radius == left.radius + right.radius
                )
            effect = actions.primitive(value.action)
            if _physical_four(effect):
                try:
                    effect.validate()
                except (TypeError, ValueError):
                    return False
                return value.radius == 4
            primitive = next(
                (
                    kernel
                    for kernel in arena.runtime.kernels._kernels
                    if kernel.effect is effect
                ),
                None,
            )
            if primitive is None:
                return False
            if primitive.right_count == 1:
                return value.radius == 0
            for symbol in range(primitive.blank + 1):
                target = effect.advance(BoundarySide.RIGHT, primitive.right[0], symbol)
                if any(
                    effect.advance(BoundarySide.RIGHT, state, symbol) != target
                    for state in primitive.right[1:]
                ):
                    return value.radius is None
            return value.radius == 1
        return False

    def _physical_cycle(self, value: PhysicalCycleProjection) -> bool:
        if (
            type(value.source) is not ArenaToken
            or type(value.root) is not ActionProgramID
            or value.root.kind != "diamond-action"
            or not self._handle(value.root)
            or not _integer(value.phase, 0, 3)
            or not _integer(value.extent, 3)
            or id(value) not in self.cycle_records
        ):
            return False
        for application in self.applications:
            if (
                not any(record is value for record in application._cycles)
                or value.root != application.root
            ):
                continue
            geometry = application.runtime.cells.source_geometry
            source = geometry._construction.source
            phase = {(1,): 0, (0, 0, 1): 1, (0, 1): 2}.get(source.digits)
            if (
                value.source is not geometry.token
                or phase is None
                or source.base != 2
                or source.blank != 2
                or geometry._read_root is None
                or value.extent != geometry._read_root.length
            ):
                return False
            actions = application.runtime.actions
            residues: dict[int, int] = {}
            pending = [(value.root.local_id, False)]
            while pending:
                index, ready = pending.pop()
                if index in residues:
                    continue
                node = actions._nodes[index]
                if node.kind == "identity":
                    residues[index] = 0
                elif node.kind == "atom":
                    primitive = actions.compiler._nodes[node.compiler_id]
                    if _physical_four(primitive):
                        try:
                            primitive.validate()
                        except (TypeError, ValueError):
                            return False
                    elif type(primitive) is not CollatzPhysicalBlockEffect:
                        return False
                    residues[index] = primitive.exponent % 3
                else:
                    if not all(
                        _integer(child, 0, index) for child in (node.first, node.second)
                    ):
                        return False
                    if not ready:
                        pending.extend(
                            ((index, True), (node.second, False), (node.first, False))
                        )
                    else:
                        residues[index] = (
                            residues[node.first] + residues[node.second]
                        ) % 3
            return value.phase == (phase + residues[value.root.local_id]) % 3
        return False

    def _original_cell(self, handle: CellID | FormalSymbolID) -> bool:
        from number_compiler.resources.diamond_boundary_validation import _original_cell

        return _original_cell(self, handle)

    def _state_node(self, handle: BoundaryStateID) -> BoundaryStateNode | None:
        for arena in self.boundaries:
            if handle.owner is arena.token and _integer(
                handle.local_id, 0, len(arena.states)
            ):
                return arena.states[handle.local_id]
        return None

    def _function_node(self, handle: BoundaryActionID) -> ContinuationNode | None:
        for arena in self.boundaries:
            if handle.owner is arena.token and _integer(
                handle.local_id, 0, len(arena.actions)
            ):
                return arena.actions[handle.local_id]
        return None

    def _boundary(self, value: object) -> bool:
        from number_compiler.resources.diamond_boundary_validation import _boundary

        return _boundary(self, value)

    def _function_signature(self, value: BoundaryFunctionSignature) -> bool:
        from number_compiler.resources.diamond_boundary_validation import (
            _function_signature,
        )

        return _function_signature(self, value)

    def _port_signature(self, value: PortSignature) -> bool:
        from number_compiler.resources.diamond_boundary_validation import (
            _port_signature,
        )

        return _port_signature(self, value)

    def _step(self, value: ContinuationStep) -> bool:
        if not (
            type(value.first) is ActionProgramID
            and type(value.second) is ActionProgramID
            and value.first.kind == value.second.kind == "diamond-action"
            and self._handle(value.first)
            and self._handle(value.second)
            and value.first.owner is value.second.owner
            and _integer(value.side, 0, 2)
            and type(value.previous) is BoundaryActionID
            and self._handle(value.previous)
            and type(value.anchor) is BoundaryStateID
            and self._handle(value.anchor)
            and value.previous.owner is value.anchor.owner
            and type(value.provider) is ImageBinding
            and self._binding(value.provider)
        ):
            return False
        anchor, previous = (
            self._state_node(value.anchor),
            self._function_node(value.previous),
        )
        return (
            anchor is not None
            and previous is not None
            and previous.signature is not None
            and anchor.action == value.first
            and anchor.side == value.side
            and previous.signature.input_action == value.first
            and previous.signature.input_side == 1 - value.side
            and previous.signature.output_action == value.second
            and previous.signature.output_side == value.side
        )

    def _temporal(self, value: TemporalActionNode) -> bool:
        from number_compiler.resources.diamond_boundary_validation import _temporal

        return _temporal(self, value)

    def _cell(self, value: CellNode | _CellKey) -> bool:
        from number_compiler.resources.diamond_boundary_validation import _cell

        return _cell(self, value)
