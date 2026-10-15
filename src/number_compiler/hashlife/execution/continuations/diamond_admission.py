"""Store-free diamond admission operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import (
    TransferSummaryID,
)
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
)
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
    ResolveExpr,
    validate_finite_observation,
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
from number_compiler.hashlife.execution.diamond_continuation_guard import (
    function_program_admission,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
)
from number_compiler.hashlife.execution.diamond_parent import publish_parent_identity
from number_compiler.hashlife.interfaces.diamond_boundary import (
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID, SymbolSort
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    CompileStructuredExpression,
    StructuredExpressionTask,
)
from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
    validate_primitive_request,
)
from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
    PrimitiveMacroKey,
    PrimitiveMacroObservation,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def _validate(self: DiamondRuntime, task: Task) -> int:
    visits = 0
    source_admission: tuple[int, int, int, int] | None = None
    if type(task) is PrimitiveMacroKey:
        validate_primitive_request(self.kernels, self.cells, task)
        return 0
    if type(task) is PrimitiveMacroObservation:
        if self.primitive_macros is None:
            raise ValueError("primitive observation belongs to another runtime")
        self.primitive_macros.validate_task(task)
        return 0
    if isinstance(task, (CompileStructuredExpression, StructuredExpressionTask)):
        self.semantic_compiler.validate_task(task)
        return 0
    if isinstance(task, (CompilePrimitiveFunction, NormalizePrimitiveLambda)):
        self.primitive_continuations.validate(task)
        return 0
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
        self.higher.validate(task)
        return 0
    if isinstance(task, LowerFinite):
        validate_finite_observation(self, task)
        return 0
    if isinstance(task, ResolveExpr):
        self.higher.expressions.node(task.expression)
        return 0
    if type(task) is PairSummary:
        if not self.pair_macros.supports(task.action):
            raise ValueError(
                "parent summary requires two complete primitive interfaces"
            )
        source_admission = self.pair_macros._require_source(task.cell)
        source = self.cells.source_geometry._construction.source
        node = self.actions.node(task.action)
        if (node.base, node.blank) != (source.base, source.blank):
            raise ValueError("parent summary and original source alphabets disagree")
    elif type(task) is SpatialSummary:
        source_admission = self.spatial.validate(task)
    elif type(task) is ContextObservation:
        self.pair_macros.contexts._validate(task)
    elif type(task) is Initial:
        self.actions.resolve(task.action)
        if type(task.side) is not int or task.side not in (0, 1):
            raise ValueError("invalid boundary side")
    elif type(task) in (Transfer, ResetTransfer, Output) and isinstance(
        task, (Transfer, ResetTransfer, Output)
    ):
        visits += self._validate_provider(task.provider)
        action = self.actions.resolve(task.action)
        source = self.cells.source_geometry._construction.source
        if action.kind != "identity" and (action.base, action.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("consumer action and source alphabets disagree")
        if type(task) is Transfer:
            self._validate_state(task.state, task.action, task.side)
        elif type(task) is ResetTransfer:
            if not self.resets.can_reset(task.provider, task.action, task.side):
                raise ValueError("transfer has no complete synchronization certificate")
        else:
            assert isinstance(task, Output)
            self._validate_state(task.left, task.action, 0)
            self._validate_state(task.right, task.action, 1)
            if self.cells.input_level(task.provider.cell):
                raise ValueError("scalar output requires an original leaf")
    elif type(task) is OutputFunction:
        formal = self.cells.formal_symbol(0)
        visits += self._validate_provider(
            ImageBinding(task.provider, formal, task.provider_left, task.provider_right)
        )
        self._validate_state(task.left, task.action, 0)
        self._validate_state(task.right, task.action, 1)
        consumer = self.actions.node(task.action)
        if task.provider != self.actions.identity or consumer.kind == "compose":
            raise ValueError(
                "finite output functions require a fixed primitive interface"
            )
        source = self.cells.source_geometry._construction.source
        if consumer.kind != "identity" and (consumer.base, consumer.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("output function and original alphabet disagree")
    elif type(task) is Evaluate:
        function = self.boundaries.action(task.function)
        value = self.boundaries.state(task.argument)
        signature = function.signature
        if signature is None or (value.action, value.side) != (
            signature.input_action,
            signature.input_side,
        ):
            raise ValueError("argument belongs to another continuation domain")
        if function.kind == "invalid" or (
            signature.input_size is not None
            and not 0 <= value.literal < signature.input_size
        ):
            raise ValueError("argument outside admissible primitive domain")
    elif type(task) is Substitute:
        step = task.step
        if type(step) is not ContinuationStep:
            raise TypeError("expected a typed continuation step")
        visits += self._validate_provider(step.provider)
        self.actions.resolve(step.first)
        self.actions.resolve(step.second)
        previous = self.boundaries.action(step.previous)
        self._validate_state(step.anchor, step.first, step.side)
        self._validate_state(task.argument, step.first, 1 - step.side)
        signature = previous.signature
        if (
            previous.kind == "invalid"
            or signature is None
            or (
                signature.input_action,
                signature.input_side,
                signature.output_action,
                signature.output_side,
            )
            != (step.first, 1 - step.side, step.second, step.side)
        ):
            raise ValueError(
                "previous continuation does not match substituted interface"
            )
        source = self.cells.source_geometry._construction.source
        for reference in (step.first, step.second):
            action = self.actions.resolve(reference)
            if action.kind != "identity" and (action.base, action.blank) != (
                source.base,
                source.blank,
            ):
                raise ValueError("substitution action and source alphabets disagree")
    else:
        raise TypeError("unknown diamond scheduler task")
    if source_admission is not None:
        self.pair_macros._record_source_admission(source_admission)
    return visits


def _admit_head_binding(self: DiamondRuntime, expression: ExprID) -> bool:
    allowed, visits, peak = function_program_admission(
        self.higher.expressions, expression
    )
    self.ledger.bump(_execution_keys.HIGHER_HEAD_BINDING_ADMISSION_VISITS, visits)
    name = "higher_head_binding_admission_workspace_peak"
    self.ledger.bump(name, max(0, peak - self.ledger.counters.get(name, 0)))
    return allowed


def _probe_admitted(self: DiamondRuntime, task: Task) -> Result | None:
    if isinstance(task, (PrimitiveMacroKey, PrimitiveMacroObservation)):
        if self.primitive_macros is None:
            self.ledger.bump(_shared_keys.PRIMITIVE_MACRO_REQUESTS)
            return None
        return self.primitive_macros.probe(task)
    if isinstance(task, (CompileStructuredExpression, StructuredExpressionTask)):
        return self.semantic_compiler.probe_task(task)
    if isinstance(task, (CompilePrimitiveFunction, NormalizePrimitiveLambda)):
        return self.primitive_continuations.probe(task)
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
        found_higher = self.higher.probe(task)
        if found_higher is not None and not isinstance(
            found_higher, (ExprID, TransferSummaryID)
        ):
            raise AssertionError(
                "higher parent cache contains a scalar or a bound legacy state"
            )
        return found_higher
    if isinstance(task, LowerFinite):
        expression = self.higher.expressions.node(task.expression)
        if expression.kind in ("literal", "symbol"):
            self.ledger.bump(_execution_keys.HIGHER_SCALAR_CONSTANT_HITS)
            return expression.value
        return None
    if isinstance(task, ResolveExpr):
        self.ledger.bump(_execution_keys.HIGHER_HEAD_REQUESTS)
        expression = self.higher.expressions.node(task.expression)
        if expression.kind not in ("call", "anchor", "continuation", "apply"):
            self.ledger.bump(_execution_keys.HIGHER_HEAD_IDENTITY_HITS)
            return task.expression
        if type(expression.sort) is SymbolSort or not expression.free_ports:
            return None
        if not self._admit_head_binding(task.expression):
            return None
        head = self.expression_heads.get(task)
        if head is not None:
            self.ledger.bump(_execution_keys.HIGHER_HEAD_CACHE_HITS)
        return head
    if isinstance(task, PairSummary):
        return self.pair_macros.cache_probe(task.action, task.cell)
    if isinstance(task, SpatialSummary):
        self.ledger.bump(_execution_keys.PRIMITIVE_SPATIAL_REQUESTS)
        found_spatial = self.spatial.bindings.get(task)
        if found_spatial is not None:
            self.ledger.bump(_execution_keys.PRIMITIVE_SPATIAL_CACHE_HITS)
        return found_spatial
    if isinstance(task, ContextObservation):
        self.ledger.bump(_execution_keys.CONTEXT_OBSERVATION_REQUESTS)
        context_result = self.pair_macros.contexts.observations.get(task)
        if context_result is not None:
            self.ledger.bump(_execution_keys.CONTEXT_OBSERVATION_CACHE_HITS)
        return context_result
    if isinstance(task, OutputFunction):
        self.ledger.bump(_execution_keys.OUTPUT_FUNCTION_REQUESTS)
        function = self.outputs.bindings.get(task)
        self.ledger.bump(
            "output_function_cache_hits"
            if function is not None
            else "output_function_evaluations"
        )
        return function
    if isinstance(task, Output):
        self.ledger.bump(_execution_keys.SCALAR_OBSERVATION_REQUESTS)
        return None
    name = (
        "initial_state"
        if isinstance(task, Initial)
        else "diamond"
        if isinstance(task, Substitute)
        else "boundary_substitution"
        if isinstance(task, Evaluate)
        else "spatial_parent"
    )
    self.ledger.bump(name + "_requests")
    found = self._memo(task).get(task)
    if found is not None:
        self.ledger.bump(name + "_cache_hits")
    else:
        self.ledger.bump(name + "_evaluations")
    if isinstance(task, (Transfer, ResetTransfer)) and isinstance(
        task.provider.cell, CellID
    ):
        key = MacroTransferKey(
            task.provider.action, task.action, task.provider.cell, task.side
        )
        publish_parent_identity(self.actions, self.cells, self.macros, key)
    return found


def _canonical_task(self: DiamondRuntime, task: Task) -> Task:
    visits = self._validate(task)
    self.ledger.bump(_execution_keys.SCHEDULER_ADMISSION_REQUESTS)
    self.ledger.bump(_execution_keys.SCHEDULER_ADMISSION_SOURCE_VISITS, visits)
    if isinstance(task, HigherUnarySummary) and task.side == 1:
        radius = self.resets.radius(task.action)
        if radius is not None and radius > 0:
            level = (radius - 1).bit_length()
            previous_level = self.cells.node(task.cell).level
            if previous_level > level:
                prefix = self.cells.slice(task.cell, 0, level)
                self.ledger.bump(_execution_keys.HIGHER_SOURCE_PREFIX_NORMALIZATIONS)
                self.ledger.bump(
                    _execution_keys.HIGHER_SOURCE_LEVELS_ELIDED,
                    previous_level - level,
                )
                return HigherUnarySummary(task.action, prefix, task.side)
        return task
    if not isinstance(task, (Transfer, ResetTransfer)) or task.side != 1:
        return task
    radius = self.resets.radius(task.action)
    if radius is not None and (
        radius == 0
        or self.cells.input_level(task.provider.cell) >= (radius - 1).bit_length()
    ):
        provider = task.provider
        if (
            provider.action == self.actions.identity
            and isinstance(provider.cell, CellID)
            and radius > 0
            and radius & (radius - 1) == 0
        ):
            level = radius.bit_length() - 1
            previous_level = self.cells.node(provider.cell).level
            if previous_level > level:
                cell = self.cells.slice(provider.cell, 0, level)
                provider = ImageBinding(
                    provider.action, cell, provider.left, provider.right
                )
                self.ledger.bump(
                    _execution_keys.SYNCHRONIZING_SOURCE_PREFIX_NORMALIZATIONS
                )
                self.ledger.bump(
                    _execution_keys.SYNCHRONIZING_SOURCE_LEVELS_ELIDED,
                    previous_level - level,
                )
        if type(task) is Transfer:
            self.ledger.bump(_execution_keys.SYNCHRONIZING_TRANSFER_NORMALIZATIONS)
        return ResetTransfer(provider, task.action, task.side)
    return task


def _fold_substitution(
    self: DiamondRuntime, step: ContinuationStep
) -> ContinuationStep:
    """Normalize sibling spatial actions before continuation interning.

    The preceding continuation and this step are two adjacent pieces of
    one scan. Their midpoint interface must agree before either piece can
    disappear into the parent action. No output symbols are constructed.
    """
    while True:
        previous = self.boundaries.action(step.previous)
        prior = previous.step
        if (
            previous.kind != "substitution"
            or prior is None
            or (prior.first, prior.second, prior.side, prior.provider.action)
            != (step.first, step.second, step.side, step.provider.action)
        ):
            return step
        first, second = (
            (prior.provider, step.provider)
            if step.side == 0
            else (step.provider, prior.provider)
        )
        if not isinstance(first.cell, CellID) or not isinstance(second.cell, CellID):
            return step
        low, high = self.cells.node(first.cell), self.cells.node(second.cell)
        if (
            low.kind not in ("source", "join")
            or high.kind not in ("source", "join")
            or low.level != high.level
        ):
            return step
        # Check the two midpoint ports using already evaluated transfers.
        unit_left = self.boundaries.literal(self.actions.identity, 0, 0)
        unit_right = self.boundaries.literal(self.actions.identity, 1, 0)
        if first.action == self.actions.identity:
            compatible = first.right == second.right and first.left == second.left
        else:
            left_scan = Transfer(
                ImageBinding(self.actions.identity, first.cell, unit_left, unit_right),
                first.action,
                first.left,
                0,
            )
            right_scan = Transfer(
                ImageBinding(self.actions.identity, second.cell, unit_left, unit_right),
                first.action,
                second.right,
                1,
            )
            compatible = (
                self._cached_transfer(left_scan) == second.left
                and self._cached_transfer(right_scan) == first.right
            )
        advanced = self._cached_transfer(
            Transfer(prior.provider, prior.first, prior.anchor, prior.side)
        )
        if not compatible or advanced != step.anchor:
            return step
        joined = self.cells.join(first.cell, second.cell)
        provider = ImageBinding(first.action, joined, first.left, second.right)
        step = ContinuationStep(
            step.first,
            step.second,
            step.side,
            prior.previous,
            provider,
            prior.anchor,
        )
        self.ledger.bump(_execution_keys.SPATIAL_SUBSTITUTION_FOLDS)
