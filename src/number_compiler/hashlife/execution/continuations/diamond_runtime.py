"""Iterative temporal diamonds over canonical source cells and continuations.

The scan and output equations are the composed bimachine equations. A temporal
midpoint is an action with symbolic ports, never a tile containing its outputs.
"""

from __future__ import annotations

from collections.abc import Generator, Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, overload

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    ImageCellArena,
    InputCellID,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
    ResolveExpr,
    lower_finite,
    resolve_expression,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_context import (
    HigherContextArena,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherEmit,
    HigherInitial,
    HigherObserve,
    HigherStep,
    HigherSummary,
    HigherUnaryObserve,
    HigherUnarySummary,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Evaluate,
    Initial,
    MacroTransferKey,
    Output,
    OutputFunction,
    PairSummary,
    ResetTransfer,
    Result,
    SpatialSummary,
    Substitute,
    Task,
    Transfer,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
    PrimitiveContinuationReducer,
)
from number_compiler.hashlife.execution.diamond_pair_macros import PrimitivePairMacros
from number_compiler.hashlife.execution.diamond_primitive_demand import (
    PrimitiveDemandOracle,
)
from number_compiler.hashlife.execution.diamond_primitive_pair import (
    PrimitivePairActions,
)
from number_compiler.hashlife.execution.diamond_spatial import PrimitiveSpatialTransfers
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryStateID,
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID, SymbolSort
from number_compiler.hashlife.interfaces.diamond_halos import CausalHaloArena
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.diamond_output import (
    DiamondOutputFunctions,
    require_transfer_expression,
)
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.diamond_resets import RightResetCertificates
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
    SemanticExpressionCompiler,
)
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    CompileStructuredExpression,
    StructuredExpressionTask,
)
from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
    PrimitiveMacroArena,
    validate_primitive_request,
)
from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
    PrimitiveMacroKey,
    PrimitiveMacroObservation,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    DiamondQuotientID,
    StructureArena,
    StructureID,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_registry import DIAMOND_WORK_COUNTERS


def _state(result: Result) -> BoundaryStateID:
    if type(result) is not BoundaryStateID:
        raise AssertionError("expected a structured boundary result")
    return result


def _scalar(result: Result) -> int:
    if type(result) is not int:
        raise AssertionError("expected one transient output scalar")
    return result


@dataclass(slots=True)
class DiamondEvaluationFrame:
    task: Task
    program: Generator[Task, Result, Result]


if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.generic_higher import (
        GenericHigherRuntime,
    )


class DiamondRuntime:
    generic_higher_executor: GenericHigherRuntime

    def __init__(self, compiler: LazyCompiler, source: SourceGeometry) -> None:
        self.family_hooks = compiler.family_hooks
        self.ledger = compiler.ledger
        self.ledger.register_execution_root(self)
        self.actions = TemporalActionArena(compiler)
        self.cells = ImageCellArena(self.actions, source)
        self.kernels = DiamondKernelArena(self.ledger)
        self.kernels.bind_family_hooks(self.family_hooks)
        self.boundaries = BoundaryActionArena(self.actions, self.kernels, self.cells)
        self.pair_macros = PrimitivePairMacros(self.boundaries)
        self.primitive_pairs = PrimitivePairActions(
            self.boundaries, self.pair_macros.unary
        )
        self.halos = CausalHaloArena(self)
        self.outputs = DiamondOutputFunctions(self)
        self.spatial = PrimitiveSpatialTransfers(self)
        self.resets = RightResetCertificates(self)
        self.higher = HigherContextArena(self)
        self.primitive_demand = PrimitiveDemandOracle(self.kernels)
        self.primitive_continuations = PrimitiveContinuationReducer(self)
        self.semantic_functions = SemanticFunctionArena(self.ledger)
        self.semantic_compiler = SemanticExpressionCompiler(
            self, self.semantic_functions
        )
        self.semantic_quotients: DiamondQuotientArena | None = None
        self.primitive_macros: PrimitiveMacroArena | None = None
        prefix = f"diamond-runtime-{len(self.ledger.inventory())}"
        self.initials: OwnedMemo[Task, BoundaryStateID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-initials", "query_memo"),
            evictable=True,
        )
        self.transfers: OwnedMemo[Task, BoundaryStateID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-spatial", "spatial_parent_memo"),
            evictable=True,
        )
        self.substitutions: OwnedMemo[Task, BoundaryStateID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-diamonds", "diamond_memo"),
            evictable=True,
        )
        self.continuations: OwnedMemo[Task, BoundaryStateID] = OwnedMemo(
            self.ledger,
            self.ledger.register(
                prefix + "-continuations", "boundary_substitution_memo"
            ),
            evictable=True,
        )
        self.macros: OwnedMemo[MacroTransferKey, ActionProgramID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-parents", "image_program_memo"),
            evictable=True,
        )
        self.primitive_ids: OwnedMemo[ActionProgramID, ActionProgramID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-primitives", "query_memo"),
            evictable=True,
        )
        self.absorbing_states: OwnedMemo[BoundaryStateID, bool] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-absorbing-states", "query_memo"),
            evictable=True,
        )
        self.expression_heads: OwnedMemo[ResolveExpr, ExprID] = OwnedMemo(
            self.ledger,
            self.ledger.register(
                prefix + "-expression-heads", "boundary_substitution_memo"
            ),
            evictable=True,
        )
        for counter in DIAMOND_WORK_COUNTERS:
            self.ledger.bump(counter, 0)

    def _primitive_macro_arena(self) -> PrimitiveMacroArena:
        """Allocate shared semantic arenas only after public request admission."""
        if self.primitive_macros is not None:
            return self.primitive_macros
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            from number_compiler.arithmetic.contracts.block_effect import (
                BlockContextBudgetExceeded,
            )

            raise BlockContextBudgetExceeded("primitive macro needs one source binding")
        structures = self.semantic_compiler.structures
        if structures is None:
            structures = StructureArena(
                BitFunctionArena(self.ledger, self.semantic_functions)
            )
            self.semantic_compiler.structures = structures
        if self.semantic_quotients is None:
            self.semantic_quotients = DiamondQuotientArena(
                self.semantic_functions, self.cells, structures=structures
            )
        elif self.semantic_quotients.structures is not structures:
            raise ValueError("runtime quotient and compiler structures disagree")
        self.primitive_macros = PrimitiveMacroArena(self, self.semantic_quotients)
        return self.primitive_macros

    @source_reads_only
    def compile_primitive_macro(
        self, kernel: ActionProgramID, source: CellID
    ) -> DiamondQuotientID:
        task = PrimitiveMacroKey(kernel, source)
        validate_primitive_request(self.kernels, self.cells, task)
        result = self.execute(task)
        if type(result) is not DiamondQuotientID:
            raise ValueError("primitive macro scheduler returned a non-quotient result")
        assert self.semantic_quotients is not None
        self.semantic_quotients.resolve(result)
        return result

    @source_reads_only
    def observe_primitive_macro(
        self,
        quotient: DiamondQuotientID,
        channel: str = "output",
        *,
        left: int,
        right: int,
        coordinate: int,
    ) -> int:
        # execute admits the complete observation before any semantic evaluation.
        return _scalar(
            self.execute(
                PrimitiveMacroObservation(quotient, channel, left, right, coordinate)
            )
        )

    def _memo(self, task: Task) -> OwnedMemo[Task, BoundaryStateID]:
        if isinstance(task, Initial):
            return self.initials
        if isinstance(task, (Transfer, ResetTransfer)):
            return self.transfers
        return (
            self.substitutions if isinstance(task, Substitute) else self.continuations
        )

    def memo_view(self, task: Task) -> Mapping[Task, BoundaryStateID]:
        """Read a task cache without exposing its mutation interface."""
        return self._memo(task)

    def kernel(self, action: ActionProgramID) -> PrimitiveKernel:
        self.actions.resolve(action)
        handle = self.primitive_ids.get(action)
        if handle is None:
            handle = self.kernels.intern(self.actions.primitive(action))
            self.primitive_ids[action] = handle
        return self.kernels.kernel(handle)

    def validate_state(
        self, state: BoundaryStateID, action: ActionProgramID, side: int
    ) -> None:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("invalid boundary side")
        self.actions.resolve(action)
        value = self.boundaries.state(state)
        if value.action != action or value.side != side:
            raise ValueError("boundary state has the wrong temporal interface")

    def validate_provider(self, provider: ImageBinding) -> int:
        if type(provider) is not ImageBinding:
            raise TypeError("expected a parametric image binding")
        action = self.actions.resolve(provider.action)
        source = self.cells.source_geometry.construction.source
        if action.kind != "identity" and (action.base, action.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("provider action and original source alphabets disagree")
        if isinstance(provider.cell, CellID):
            self.cells.require_original(provider.cell)
            visits = 1
        else:
            self.cells.validate_input(provider.cell)
            visits = 0
        self.validate_state(provider.left, provider.action, 0)
        self.validate_state(provider.right, provider.action, 1)
        return visits

    def validate_task(self, task: Task) -> int:
        from number_compiler.hashlife.execution.continuations.diamond_admission import (
            validate_diamond_task,
        )

        return validate_diamond_task(self, task)

    def _probe(self, task: Task) -> Result | None:
        return self.probe_admitted_task(self.canonical_task(task))

    def admit_head_binding(self, expression: ExprID) -> bool:
        from number_compiler.hashlife.execution.continuations.diamond_admission import (
            admit_head_binding,
        )

        return admit_head_binding(self, expression)

    def probe_admitted_task(self, task: Task) -> Result | None:
        from number_compiler.hashlife.execution.continuations.diamond_admission import (
            probe_admitted_task,
        )

        return probe_admitted_task(self, task)

    def canonical_task(self, task: Task) -> Task:
        from number_compiler.hashlife.execution.continuations.diamond_admission import (
            canonical_task,
        )

        return canonical_task(self, task)

    def cached_transfer(self, task: Transfer) -> BoundaryStateID | None:
        return self.transfers.get(self.canonical_task(task))

    @overload
    def execute(
        self, root: Initial | Transfer | ResetTransfer | Substitute | Evaluate
    ) -> BoundaryStateID: ...

    @overload
    def execute(
        self,
        root: HigherInitial
        | HigherStep
        | HigherEmit
        | HigherObserve
        | HigherUnaryObserve
        | ResolveExpr
        | NormalizePrimitiveLambda,
    ) -> ExprID: ...

    @overload
    def execute(
        self,
        root: PairSummary
        | SpatialSummary
        | ContextObservation
        | OutputFunction
        | HigherSummary
        | HigherUnarySummary
        | CompilePrimitiveFunction,
    ) -> TransferSummaryID: ...

    @overload
    def execute(
        self, root: Output | LowerFinite | PrimitiveMacroObservation
    ) -> int: ...

    @overload
    def execute(self, root: PrimitiveMacroKey) -> DiamondQuotientID: ...

    @overload
    def execute(
        self, root: CompileStructuredExpression | StructuredExpressionTask
    ) -> StructureID: ...

    @overload
    def execute(self, root: Task) -> Result: ...

    def execute(self, root: Task) -> Result:
        from number_compiler.hashlife.execution.continuations.diamond_dependencies import (
            execute,
        )

        return execute(self, root)

    def publish_task(self, task: Task, result: Result) -> None:
        if isinstance(task, (PrimitiveMacroKey, PrimitiveMacroObservation)):
            if self.primitive_macros is None:
                raise ValueError("primitive publication has no admitted arena")
            self.primitive_macros.publication(task, result)
            return
        if isinstance(task, (CompileStructuredExpression, StructuredExpressionTask)):
            self.semantic_compiler.publication(task, result)
            return
        if isinstance(task, (CompilePrimitiveFunction, NormalizePrimitiveLambda)):
            self.primitive_continuations.publish(task, result)
            return
        if isinstance(
            task,
            (
                HigherEmit,
                HigherInitial,
                HigherObserve,
                HigherStep,
                HigherSummary,
                HigherUnaryObserve,
                HigherUnarySummary,
            ),
        ):
            self.higher.publish(task, result)
            return
        if isinstance(task, LowerFinite):
            return
        if isinstance(task, ResolveExpr):
            if type(result) is not ExprID:
                raise AssertionError("head normalization returned a scalar")
            expression = self.higher.expressions.node(task.expression)
            if (
                type(expression.sort) is not SymbolSort
                and expression.free_ports
                and self.higher.expressions.node(result).free_ports
                and self.higher.expressions.node(result).kind
                not in ("literal", "symbol")
                and self.admit_head_binding(task.expression)
                and self.admit_head_binding(result)
            ):
                self.expression_heads[task] = result
            self.ledger.bump(_execution_keys.HIGHER_HEAD_EVALUATIONS)
            return
        if isinstance(task, PairSummary):
            return  # Node, semantic interner, and binding were published atomically.
        if isinstance(task, SpatialSummary):
            self.spatial.bindings[task] = require_transfer_expression(result)
            self.ledger.bump(_execution_keys.PRIMITIVE_SPATIAL_EVALUATIONS)
            return
        if isinstance(task, ContextObservation):
            self.pair_macros.contexts.observations[task] = require_transfer_expression(
                result
            )
            self.ledger.bump(_execution_keys.CONTEXT_OBSERVATION_EVALUATIONS)
        elif isinstance(task, OutputFunction):
            self.outputs.bindings[task] = require_transfer_expression(result)
        elif not isinstance(task, Output):
            self._memo(task)[task] = _state(result)

    def task_program(self, task: Task) -> Generator[Task, Result, Result]:
        if isinstance(task, (PrimitiveMacroKey, PrimitiveMacroObservation)):
            return self._primitive_macro_arena().program(task)
        if isinstance(task, (CompileStructuredExpression, StructuredExpressionTask)):
            return self.semantic_compiler.program(task)
        if isinstance(task, (CompilePrimitiveFunction, NormalizePrimitiveLambda)):
            return self.primitive_continuations.program(task)
        if isinstance(
            task,
            (
                HigherEmit,
                HigherInitial,
                HigherObserve,
                HigherStep,
                HigherSummary,
                HigherUnaryObserve,
                HigherUnarySummary,
            ),
        ):
            return self.higher.program(task)
        if isinstance(task, LowerFinite):
            return lower_finite(self, task)
        if isinstance(task, ResolveExpr):
            return resolve_expression(self, task)
        if isinstance(task, PairSummary):
            return self._pair_summary(task)
        if isinstance(task, SpatialSummary):
            return self.spatial.compile(task)
        if isinstance(task, ContextObservation):
            return self._context(task)
        if isinstance(task, Initial):
            return self._initial(task)
        if isinstance(task, Transfer):
            return self._transfer(task)
        if isinstance(task, ResetTransfer):
            return self._reset_transfer(task)
        if isinstance(task, Substitute):
            return self._substitute(task)
        if isinstance(task, Evaluate):
            return self._evaluate(task)
        if isinstance(task, OutputFunction):
            return self.outputs.compile(task)
        return self._output(task)

    def _reset_transfer(self, task: ResetTransfer) -> Generator[Task, Result, Result]:
        initial = _state((yield Initial(task.action, task.side)))
        return (
            yield from self._transfer(
                Transfer(task.provider, task.action, initial, task.side)
            )
        )

    def _pair_summary(self, task: PairSummary) -> Generator[Task, Result, Result]:
        from number_compiler.hashlife.execution.diamond_pair_macros import PairMacroKey

        arena = self.pair_macros
        if self.cells.node(task.cell).level:
            left, right = arena.build_children(task.cell)
            low = require_transfer_expression((yield PairSummary(task.action, left)))
            high = require_transfer_expression((yield PairSummary(task.action, right)))
            record = arena.compose_parent(
                task.action, arena.resolve(low), arena.resolve(high)
            )
        else:
            record = arena.leaf_record(task.action, task.cell)
        result = arena.publish_record(PairMacroKey(task.action, task.cell), record)
        self.ledger.bump(_execution_keys.MACRO_TRANSFER_EVALUATIONS)
        return result

    def _context(self, request: ContextObservation) -> Generator[Task, Result, Result]:
        arena = self.pair_macros.contexts
        aid, bid = arena.validate_observation(request)
        node = arena.resolve(request.program)
        if node.kind == "leaf":
            symbol = self.kernels.constant(
                self.kernels.kernel(aid).blank + 1, node.symbol
            )
            port = arena.input_port((request.left, request.right, request.incoming))
            if port is None:
                emitted = self.kernels.emit_expression(
                    aid, request.left, symbol, request.right
                )
                return self.kernels.advance_expression(
                    bid, BoundarySide(request.side), request.incoming, emitted
                )
            input_side, variable = port
            emitted = arena.unary.mapped(
                aid,
                input_side,
                variable,
                aid,
                "emit",
                0,
                (request.left, symbol, request.right),
            )
            return arena.unary.mapped(
                aid,
                input_side,
                variable,
                bid,
                "advance",
                request.side,
                (request.incoming, emitted),
            )
        assert node.left is not None and node.right is not None
        assert node.middle_left is not None and node.middle_right is not None
        from number_compiler.hashlife.execution.continuations.diamond_context_program import (
            LEFT_A,
            RIGHT_A,
        )

        middle_left = arena.substitute_context(node.middle_left, LEFT_A, request.left)
        middle_right = arena.substitute_context(
            node.middle_right, RIGHT_A, request.right
        )
        if request.side == 0:
            midpoint = require_transfer_expression(
                (
                    yield ContextObservation(
                        node.left, request.left, middle_right, request.incoming, 0
                    )
                )
            )
            return require_transfer_expression(
                (
                    yield ContextObservation(
                        node.right, middle_left, request.right, midpoint, 0
                    )
                )
            )
        midpoint = require_transfer_expression(
            (
                yield ContextObservation(
                    node.right, middle_left, request.right, request.incoming, 1
                )
            )
        )
        return require_transfer_expression(
            (
                yield ContextObservation(
                    node.left, request.left, middle_right, midpoint, 1
                )
            )
        )

    def _initial(self, task: Initial) -> Generator[Task, Result, Result]:
        node = self.actions.node(task.action)
        if node.kind != "compose":
            value = (
                0
                if node.kind == "identity"
                else self.kernel(task.action).initial(BoundarySide(task.side))
            )
            return self.boundaries.literal(task.action, task.side, value)
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        anchor = _state((yield Initial(first, task.side)))
        target = _state((yield Initial(second, task.side)))
        function = self.boundaries.constant(target, first, 1 - task.side)
        return self.boundaries.pair(task.action, task.side, anchor, function)

    def _identity_provider(
        self, cell: InputCellID
    ) -> Generator[Task, Result, ImageBinding]:
        identity = self.actions.identity
        left = _state((yield Initial(identity, 0)))
        right = _state((yield Initial(identity, 1)))
        return ImageBinding(identity, cell, left, right)

    def _joined_provider(
        self,
        provider: ImageBinding,
        after: ActionProgramID,
        left: BoundaryStateID,
        right: BoundaryStateID,
    ) -> ImageBinding:
        if provider.action == self.actions.identity:
            return ImageBinding(after, provider.cell, left, right)
        if after == self.actions.identity:
            return provider
        action = self.actions.compose(provider.action, after)
        lfun = self.boundaries.constant(left, provider.action, 1)
        rfun = self.boundaries.constant(right, provider.action, 0)
        return ImageBinding(
            action,
            provider.cell,
            self.boundaries.pair(action, 0, provider.left, lfun),
            self.boundaries.pair(action, 1, provider.right, rfun),
        )

    def _fold_substitution(self, step: ContinuationStep) -> ContinuationStep:
        from number_compiler.hashlife.execution.continuations.diamond_admission import (
            fold_substitution,
        )

        return fold_substitution(self, step)

    def _transfer(self, task: Transfer) -> Generator[Task, Result, Result]:
        node = self.actions.node(task.action)
        if node.kind == "identity":
            return task.state
        if node.kind == "atom":
            primitive = self.kernel(task.action)
            absorbing = self.absorbing_states.get(task.state)
            if absorbing is None:
                finite = self.boundaries.state(task.state)
                absorbing = primitive.is_absorbing(
                    BoundarySide(task.side), finite.literal
                )
                self.absorbing_states[task.state] = absorbing
                self.ledger.bump(_execution_keys.PRIMITIVE_ABSORBER_EVALUATIONS)
            if absorbing:
                self.ledger.bump(_execution_keys.PRIMITIVE_ABSORBER_HITS)
                if type(primitive.effect) is NonblankBlockEffect:
                    self.ledger.bump(_execution_keys.NONBLANK_ABSORBER_HITS)
                return task.state
        provider = task.provider
        if (
            node.kind == "atom"
            and provider.action == self.actions.identity
            and isinstance(provider.cell, CellID)
        ):
            summary = require_transfer_expression(
                (yield SpatialSummary(task.action, provider.cell, task.side))
            )
            return self.spatial.observe(task.action, task.side, summary, task.state)
        primitive_pair = self.primitive_pairs.supports(task.action)
        if (
            provider.action == self.actions.identity
            and primitive_pair
            and isinstance(provider.cell, CellID)
        ):
            return (
                yield from self.pair_macros.advance_program(
                    task.action, provider.cell, task.state, task.side
                )
            )
        if (
            node.kind == "atom"
            and self.actions.node(provider.action).kind == "atom"
            and isinstance(provider.cell, CellID)
        ):
            composed = self.actions.compose(provider.action, task.action)
            summary = require_transfer_expression(
                (yield PairSummary(composed, provider.cell))
            )
            return (
                yield from self.pair_macros.apply_context_program(
                    summary, provider.left, provider.right, task.state, task.side
                )
            )
        if node.kind == "compose" and not primitive_pair:
            first, second = (
                self.actions.reference(node.first),
                self.actions.reference(node.second),
            )
            state = self.boundaries.state(task.state)
            assert state.anchor is not None and state.continuation is not None
            anchor = _state((yield Transfer(provider, first, state.anchor, task.side)))
            step = ContinuationStep(
                first, second, task.side, state.continuation, provider, state.anchor
            )
            if self.actions.node(first).kind == "atom":
                domain = self.kernel(first).domain(BoundarySide(1 - task.side))
                values: list[BoundaryStateID] = []
                for index in range(len(domain)):
                    argument = self.boundaries.literal(first, 1 - task.side, index)
                    values.append(_state((yield Substitute(step, argument))))
                function = self.boundaries.finite_function(values, first, 1 - task.side)
            else:
                function = self.boundaries.substitution(self._fold_substitution(step))
            return self.boundaries.pair(task.action, task.side, anchor, function)
        if not self.cells.input_level(provider.cell):
            original = yield from self._identity_provider(provider.cell)
            symbol = _scalar(
                (yield Output(original, provider.action, provider.left, provider.right))
            )
            if primitive_pair:
                return self.primitive_pairs.advance(
                    task.action, task.state, task.side, symbol
                )
            finite_state = self.boundaries.state(task.state)
            value = self.kernel(task.action).advance(
                BoundarySide(task.side), finite_state.literal, symbol
            )
            return self.boundaries.literal(task.action, task.side, value)
        assert isinstance(provider.cell, CellID)
        left, right = self.cells.split(provider.cell)
        original_left = yield from self._identity_provider(left)
        original_right = yield from self._identity_provider(right)
        middle_left = _state(
            (yield Transfer(original_left, provider.action, provider.left, 0))
        )
        middle_right = _state(
            (yield Transfer(original_right, provider.action, provider.right, 1))
        )
        low = ImageBinding(provider.action, left, provider.left, middle_right)
        high = ImageBinding(provider.action, right, middle_left, provider.right)
        before, after = (low, high) if task.side == 0 else (high, low)
        midpoint = _state((yield Transfer(before, task.action, task.state, task.side)))
        return _state((yield Transfer(after, task.action, midpoint, task.side)))

    def _substitute(self, task: Substitute) -> Generator[Task, Result, Result]:
        step = task.step
        continuation = self.boundaries.action(step.previous)
        if continuation.kind == "constant":
            assert continuation.value is not None
            previous = continuation.value
            self.ledger.bump(_execution_keys.CONSTANT_CONTINUATION_ARGUMENT_ELISIONS)
        else:
            argument = _state(
                (
                    yield Transfer(
                        step.provider, step.first, task.argument, 1 - step.side
                    )
                )
            )
            previous = _state((yield Evaluate(step.previous, argument)))
        left, right = (
            (step.anchor, task.argument)
            if step.side == 0
            else (task.argument, step.anchor)
        )
        provider = self._joined_provider(step.provider, step.first, left, right)
        result = _state((yield Transfer(provider, step.second, previous, step.side)))
        return result

    def _evaluate(self, task: Evaluate) -> Generator[Task, Result, Result]:
        selected = self.boundaries.select(task.function, task.argument)
        if selected is not None:
            return selected
        step = self.boundaries.action(task.function).step
        assert step is not None
        return _state((yield Substitute(step, task.argument)))

    def _output(self, task: Output) -> Generator[Task, Result, Result]:
        provider = task.provider
        node = self.actions.node(task.action)
        if node.kind == "compose" or provider.action != self.actions.identity:
            # Higher interfaces stay executable programs. Enumerating every
            # original-symbol cofactor here forces unrelated source contexts and
            # defeats the parent DAG. Only fixed primitive functions are eager.
            return (yield from self._raw_output(task))
        request = OutputFunction(
            provider.action,
            provider.left,
            provider.right,
            task.action,
            task.left,
            task.right,
        )
        function = require_transfer_expression((yield request))
        constant = self.outputs.constant(function)
        if constant is not None:
            self.ledger.bump(_execution_keys.PRIMITIVE_OUTPUT_PROVIDER_ELISIONS)
            return constant
        return self.outputs.observe(function, self.cells.input_symbol(provider.cell))

    def _raw_output(self, task: Output) -> Generator[Task, Result, Result]:
        node = self.actions.node(task.action)
        provider = task.provider
        if node.kind in ("identity", "atom"):
            original = yield from self._identity_provider(provider.cell)
            function: TransferSummaryID | None = None
            if node.kind == "atom":
                function = require_transfer_expression(
                    (
                        yield OutputFunction(
                            self.actions.identity,
                            original.left,
                            original.right,
                            task.action,
                            task.left,
                            task.right,
                        )
                    )
                )
                constant = self.outputs.constant(function)
                if constant is not None:
                    self.ledger.bump(_execution_keys.PRIMITIVE_OUTPUT_PROVIDER_ELISIONS)
                    return constant
            if provider.action == self.actions.identity:
                symbol = self.cells.input_symbol(provider.cell)
            else:
                symbol = _scalar(
                    (
                        yield Output(
                            original, provider.action, provider.left, provider.right
                        )
                    )
                )
            return (
                symbol if function is None else self.outputs.observe(function, symbol)
            )
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        left, right = (
            self.boundaries.state(task.left),
            self.boundaries.state(task.right),
        )
        assert left.anchor is not None and left.continuation is not None
        assert right.anchor is not None and right.continuation is not None
        left_function = self.boundaries.action(left.continuation)
        if left_function.kind == "constant":
            assert left_function.value is not None
            second_left = left_function.value
            self.ledger.bump(_execution_keys.CONSTANT_CONTINUATION_ARGUMENT_ELISIONS)
        else:
            left_argument = _state((yield Transfer(provider, first, right.anchor, 1)))
            second_left = _state((yield Evaluate(left.continuation, left_argument)))
        right_function = self.boundaries.action(right.continuation)
        if right_function.kind == "constant":
            assert right_function.value is not None
            second_right = right_function.value
            self.ledger.bump(_execution_keys.CONSTANT_CONTINUATION_ARGUMENT_ELISIONS)
        else:
            right_argument = _state((yield Transfer(provider, first, left.anchor, 0)))
            second_right = _state((yield Evaluate(right.continuation, right_argument)))
        intermediate = self._joined_provider(provider, first, left.anchor, right.anchor)
        return _scalar((yield Output(intermediate, second, second_left, second_right)))

    def point_span(
        self, action: ActionProgramID, position: int, source_length: int
    ) -> tuple[tuple[int, CellID], ...]:
        radius = self.halos.right(action)
        stop = (
            source_length
            if radius is None
            else min(source_length, position + radius + 1)
        )
        return self.cells.source_span(0, stop)

    def point(self, action: ActionProgramID, position: int) -> int:
        self.actions.resolve(action)
        if type(position) is not int or position < 0:
            raise ValueError("point coordinate must be nonnegative")
        source = self.cells.source_geometry.source_root
        if source is None or position >= source.length:
            raise IndexError(position)
        left = _state(self.execute(Initial(action, 0)))
        right = _state(self.execute(Initial(action, 1)))
        unit_left = _state(self.execute(Initial(self.actions.identity, 0)))
        unit_right = _state(self.execute(Initial(self.actions.identity, 1)))
        forest = self.point_span(action, position, source.length)
        selected: CellID | None = None
        origin = 0
        for start, cell in forest:
            stop = start + self.cells.node(cell).width
            if stop <= position:
                left = _state(
                    self.execute(
                        Transfer(
                            ImageBinding(
                                self.actions.identity, cell, unit_left, unit_right
                            ),
                            action,
                            left,
                            0,
                        )
                    )
                )
            elif start <= position:
                selected, origin = cell, start
        for start, cell in reversed(forest):
            if start > position:
                right = _state(
                    self.execute(
                        Transfer(
                            ImageBinding(
                                self.actions.identity, cell, unit_left, unit_right
                            ),
                            action,
                            right,
                            1,
                        )
                    )
                )
        assert selected is not None
        while self.cells.node(selected).level:
            low, high = self.cells.split(selected)
            middle = origin + self.cells.node(low).width
            if position < middle:
                right = _state(
                    self.execute(
                        Transfer(
                            ImageBinding(
                                self.actions.identity, high, unit_left, unit_right
                            ),
                            action,
                            right,
                            1,
                        )
                    )
                )
                selected = low
            else:
                left = _state(
                    self.execute(
                        Transfer(
                            ImageBinding(
                                self.actions.identity, low, unit_left, unit_right
                            ),
                            action,
                            left,
                            0,
                        )
                    )
                )
                selected, origin = high, middle
        original = ImageBinding(self.actions.identity, selected, unit_left, unit_right)
        return _scalar(self.execute(Output(original, action, left, right)))
