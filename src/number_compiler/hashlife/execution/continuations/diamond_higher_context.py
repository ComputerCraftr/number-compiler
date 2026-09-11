"""Complete higher boundary functions composed before their port observations.

K(F,G,w)(l,r,q) transfers G across F's output on w.  Its two spatial
composition equations use F's unary boundary transfers, never an emitted
intermediate word.  Source bindings and bound observations are distinct from
semantic records, whose only payloads are action and expression references.
"""

from __future__ import annotations

from collections.abc import Generator, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HIGHER_TASK_TYPES,
    HigherEmit,
    HigherInitial,
    HigherObserve,
    HigherStep,
    HigherSummary,
    HigherTask,
    HigherUnaryObserve,
    HigherUnarySummary,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    SpatialSummary,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    NormalizePrimitiveLambda,
)
from number_compiler.hashlife.execution.diamond_observation_guard import (
    retain_expression_response,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprID,
)
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Result,
        Task,
    )


def _expr(value: Result) -> ExprID:
    if type(value) is not ExprID:
        raise AssertionError("higher context expected a typed expression")
    return value


def _summary_id(value: Result) -> TransferSummaryID:
    if type(value) is not TransferSummaryID:
        raise AssertionError("higher context expected a summary")
    return value


def _side(value: int) -> None:
    if type(value) is not int or value not in (0, 1):
        raise ValueError("higher context direction must be zero or one")


@dataclass(frozen=True, slots=True)
class HigherContextRecord:
    provider: ActionProgramID
    consumer: ActionProgramID
    left: ClosureProgramID
    right: ClosureProgramID

    def __post_init__(self) -> None:
        if (
            type(self.provider) is not ActionProgramID
            or type(self.consumer) is not ActionProgramID
            or self.provider.kind != "diamond-action"
            or self.consumer.kind != "diamond-action"
            or self.provider.owner is not self.consumer.owner
            or type(self.left) is not ClosureProgramID
            or type(self.right) is not ClosureProgramID
            or self.left.kind != "diamond-expression-closure"
            or self.right.kind != "diamond-expression-closure"
            or self.left.owner is not self.right.owner
        ):
            raise ValueError(
                "higher context requires scoped action and expression references"
            )


@dataclass(frozen=True, slots=True)
class HigherUnaryRecord:
    action: ActionProgramID
    side: int
    body: ClosureProgramID

    def __post_init__(self) -> None:
        _side(self.side)
        if (
            type(self.action) is not ActionProgramID
            or self.action.kind != "diamond-action"
            or type(self.body) is not ClosureProgramID
            or self.body.kind != "diamond-expression-closure"
        ):
            raise ValueError(
                "higher unary transfer requires scoped action and expression references"
            )


HigherRecord = HigherContextRecord | HigherUnaryRecord


class HigherContextArena:
    """Symbolic K/U functions over structured, non-enumerated boundary types."""

    def __init__(
        self,
        runtime: DiamondRuntime,
        expressions: BoundaryExpressionArena | None = None,
    ) -> None:
        self.runtime = runtime
        boundaries = runtime.boundaries
        self.boundaries = boundaries
        self.expressions = (
            expressions
            if expressions is not None
            else BoundaryExpressionArena(boundaries, unary=runtime.pair_macros.unary)
        )
        if self.expressions.boundaries is not boundaries:
            raise ValueError("higher context expressions have another boundary owner")
        self.actions, self.cells, self.kernels = (
            boundaries.temporals,
            boundaries.cells,
            boundaries.kernels,
        )
        self.ledger = boundaries.ledger
        self.ledger.register_execution_root(self)
        self.token = ArenaToken("diamond-higher-context")
        prefix = f"diamond-higher-context-{len(self.ledger.inventory())}"
        self.node_owner = self.ledger.register(
            prefix + "-nodes", "macro_transfer_program"
        )
        self.id_owner = self.ledger.register(
            prefix + "-ids", "macro_transfer_program_interner"
        )
        self._nodes: MutableSequence[HigherRecord] = self.ledger.make_list(
            self.node_owner
        )
        self._ids: MutableMapping[HigherRecord, TransferSummaryID] = (
            self.ledger.make_dict(self.id_owner)
        )
        self.binding_owner = self.ledger.register(
            prefix + "-bindings", "spatial_parent_memo"
        )
        self.bindings: MutableMapping[
            HigherSummary | HigherUnarySummary, TransferSummaryID
        ] = self.ledger.make_dict(self.binding_owner)
        self.ledger.register_container(
            self.binding_owner,
            self.bindings,
            payloads=lambda: self.bindings.items(),
            evict=self._evict_bindings,
        )
        self.observations: OwnedMemo[
            HigherInitial | HigherStep | HigherObserve | HigherUnaryObserve, ExprID
        ] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-observations", "query_memo"),
            evictable=True,
        )

    def _evict_bindings(self) -> None:
        count = len(self.bindings)
        self.bindings.clear()
        self.ledger.release(self.binding_owner, entries=count)

    def _action(self, action: ActionProgramID) -> None:
        node = self.actions.resolve(action)
        source = self.cells.source_geometry._construction.source
        if node.kind != "identity" and (node.base, node.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("higher context action has another source alphabet")

    def _state(self, expression: ExprID, action: ActionProgramID, side: int) -> None:
        if self.expressions.node(expression).sort != self.expressions.state_sort(
            action, side
        ):
            raise ValueError("higher context boundary expression has another port sort")

    def _source(self, cell: CellID) -> tuple[int, int]:
        self.cells.require_original(cell)
        return 1, 0

    def resolve(self, handle: TransferSummaryID) -> HigherRecord:
        if type(handle) is not TransferSummaryID or handle.kind not in (
            "diamond-higher-context",
            "diamond-higher-unary",
        ):
            raise ValueError("expected a higher context or unary summary")
        handle.validate(self.token, handle.kind, size=len(self._nodes))
        record = self._nodes[handle.local_id]
        if (handle.kind == "diamond-higher-context") != isinstance(
            record, HigherContextRecord
        ):
            raise ValueError("higher summary kind disagrees with its semantic record")
        return record

    def context(self, handle: TransferSummaryID) -> HigherContextRecord:
        record = self.resolve(handle)
        if not isinstance(record, HigherContextRecord):
            raise ValueError("expected a bilateral higher context")
        return record

    def unary(self, handle: TransferSummaryID) -> HigherUnaryRecord:
        record = self.resolve(handle)
        if not isinstance(record, HigherUnaryRecord):
            raise ValueError("expected a unary higher transfer")
        return record

    def _validate(self, task: HigherTask) -> tuple[int, int]:
        if type(task) not in HIGHER_TASK_TYPES:
            raise ValueError("unknown higher context task")
        if isinstance(task, (HigherInitial, HigherStep, HigherUnarySummary)):
            _side(task.side)
            self._action(task.action)
            if isinstance(task, HigherStep):
                self._state(task.state, task.action, task.side)
                if self.expressions.node(
                    task.symbol
                ).sort != self.expressions.symbol_sort(task.action):
                    raise ValueError("higher step symbol has another alphabet")
            if isinstance(task, HigherUnarySummary):
                return self._source(task.cell)
        elif type(task) is HigherEmit:
            self._action(task.action)
            self._state(task.left, task.action, 0)
            self._state(task.right, task.action, 1)
            if self.expressions.node(task.symbol).sort != self.expressions.symbol_sort(
                task.action
            ):
                raise ValueError("higher output symbol has another alphabet")
        elif type(task) is HigherSummary:
            self._action(task.provider)
            self._action(task.consumer)
            return self._source(task.cell)
        elif type(task) is HigherObserve:
            _side(task.side)
            record = self.context(task.summary)
            self._state(task.left, record.provider, 0)
            self._state(task.right, record.provider, 1)
            self._state(task.incoming, record.consumer, task.side)
        elif type(task) is HigherUnaryObserve:
            unary = self.unary(task.summary)
            self._state(task.state, unary.action, unary.side)
        else:
            raise ValueError("unknown higher context task")
        return 0, 0

    def validate(self, task: HigherTask) -> None:
        self._record_admission(*self._validate(task))

    def _record_admission(self, visits: int, peak: int) -> None:
        self.ledger.bump("higher_context_admission_visits", visits)
        self.ledger.bump(
            "higher_context_admission_workspace_peak",
            max(
                0,
                peak
                - self.ledger.counters.get(
                    "higher_context_admission_workspace_peak", 0
                ),
            ),
        )

    def _canonical_step(self, task: HigherStep) -> HigherStep:
        """Erase only an incoming port covered by the complete reset proof.

        Callers validate the entire original request before entering this
        helper. The replacement is one universal primitive initial literal.
        """
        if task.side != 1 or self.actions.node(task.action).kind != "atom":
            return task
        radius = self.runtime.resets.radius(task.action)
        if radius is None or radius > 1:
            return task
        primitive = self.runtime.kernel(task.action)
        initial = self.expressions.literal(
            self.boundaries.literal(
                task.action, 1, primitive.initial(BoundarySide.RIGHT)
            )
        )
        symbol = self.expressions.symbol(task.action, 0) if radius == 0 else task.symbol
        if initial == task.state and symbol == task.symbol:
            return task
        self.ledger.bump("higher_reset_key_normalizations")
        return HigherStep(task.action, 1, initial, symbol)

    def _observation_result(
        self,
        task: HigherInitial | HigherStep | HigherObserve | HigherUnaryObserve,
        result: Result,
    ) -> ExprID:
        if type(result) is not ExprID:
            raise ValueError("higher observation requires a scoped expression result")
        if isinstance(task, (HigherInitial, HigherStep)):
            action, side = task.action, task.side
        elif isinstance(task, HigherObserve):
            action, side = self.context(task.summary).consumer, task.side
        else:
            record = self.unary(task.summary)
            action, side = record.action, record.side
        self._state(result, action, side)
        return result

    def probe(self, task: HigherTask) -> Result | None:
        visits, peak = self._validate(task)
        if isinstance(task, HigherStep):
            task = self._canonical_step(task)
        self._record_admission(visits, peak)
        self.ledger.bump("higher_context_requests")
        if isinstance(task, HigherEmit):
            # Never build a bound local-output response index.
            return None
        found: Result | None
        if isinstance(task, (HigherSummary, HigherUnarySummary)):
            found = self.bindings.get(task)
        else:
            found = self.observations.get(task)
        if found is not None:
            self.ledger.bump("higher_context_cache_hits")
        return found

    def publish(self, task: HigherTask, result: Result) -> None:
        admission = self._validate(task)
        if isinstance(task, HigherEmit):
            return
        if isinstance(task, (HigherSummary, HigherUnarySummary)):
            if self.bindings.get(task) != _summary_id(result):
                raise AssertionError("summary publication was not atomic")
        else:
            expression = self._observation_result(task, result)
            if isinstance(task, HigherStep):
                task = self._canonical_step(task)
            inputs: tuple[ExprID, ...] = ()
            if isinstance(task, HigherStep):
                inputs = task.state, task.symbol
            elif isinstance(task, HigherObserve):
                inputs = task.left, task.right, task.incoming
            elif isinstance(task, HigherUnaryObserve):
                inputs = (task.state,)
            if retain_expression_response(self.expressions, expression, inputs):
                self.observations[task] = expression
            else:
                self.ledger.bump("higher_context_bound_result_memo_drops")
        self._record_admission(*admission)
        self.ledger.bump("higher_context_evaluations")

    def _publish_summary(
        self, key: HigherSummary | HigherUnarySummary, record: HigherRecord
    ) -> TransferSummaryID:
        admission = self._validate(key)
        if isinstance(record, HigherContextRecord):
            if not isinstance(key, HigherSummary) or (key.provider, key.consumer) != (
                record.provider,
                record.consumer,
            ):
                raise ValueError("context binding and program interfaces disagree")
            self._program_sort(record.left, record.consumer, 0)
            self._program_sort(record.right, record.consumer, 1)
        else:
            if not isinstance(key, HigherUnarySummary) or (key.action, key.side) != (
                record.action,
                record.side,
            ):
                raise ValueError("unary binding and program interfaces disagree")
            self._program_sort(record.body, record.action, record.side)
        existing = self.bindings.get(key)
        if existing is not None:
            if self.resolve(existing) != record:
                raise ValueError(
                    "source binding already has a different higher program"
                )
            self._record_admission(*admission)
            return existing
        found = self._ids.get(record)
        reservations = [(self.binding_owner, 1, 0)]
        if found is None:
            reservations.extend(((self.node_owner, 1, 1), (self.id_owner, 1, 0)))
        self.ledger.reserve_many(tuple(reservations))
        self._record_admission(*admission)
        if found is None:
            kind = (
                "diamond-higher-context"
                if isinstance(record, HigherContextRecord)
                else "diamond-higher-unary"
            )
            found = TransferSummaryID(self.token, kind, len(self._nodes))
            self._nodes.append(record)
            self._ids[record] = found
            self.ledger.bump("higher_context_program_interner_evaluations")
        else:
            self.ledger.bump("higher_context_program_interner_hits")
        self.bindings[key] = found
        return found

    def _program_sort(
        self, program: ClosureProgramID, action: ActionProgramID, side: int
    ) -> None:
        if self.expressions.closures.result_sort(
            program
        ) != self.expressions.state_sort(action, side):
            raise ValueError("higher closure has another result interface")

    def _unary_variable(self, action: ActionProgramID, side: int) -> ExprID:
        return self.expressions.variable(
            self.expressions.state_sort(action, side), "higher-unary-state"
        )

    def _context_variables(
        self, provider: ActionProgramID, consumer: ActionProgramID, side: int
    ) -> tuple[ExprID, ExprID, ExprID]:
        arena = self.expressions
        return (
            arena.variable(arena.state_sort(provider, 0), "higher-context-left"),
            arena.variable(arena.state_sort(provider, 1), "higher-context-right"),
            arena.variable(arena.state_sort(consumer, side), "higher-context-incoming"),
        )

    def _unary_apply(self, record: HigherUnaryRecord, state: ExprID) -> ExprID:
        return self.expressions.call(record.body, (state,))

    def _context_apply(
        self,
        record: HigherContextRecord,
        left: ExprID,
        right: ExprID,
        incoming: ExprID,
        side: int,
    ) -> ExprID:
        return self.expressions.call(
            record.left if side == 0 else record.right, (left, right, incoming)
        )

    def program(self, task: HigherTask) -> Generator[Task, Result, Result]:
        self.validate(task)
        if isinstance(task, HigherStep):
            original = task
            task = self._canonical_step(task)
            if task != original:
                self.ledger.bump("higher_primitive_right_reset_elisions")
        if isinstance(task, HigherInitial):
            return (yield from self._initial(task))
        if isinstance(task, HigherStep):
            return (yield from self._step(task))
        if isinstance(task, HigherEmit):
            return (yield from self._emit(task))
        if isinstance(task, HigherUnarySummary):
            return (yield from self._unary_summary(task))
        if isinstance(task, HigherSummary):
            return (yield from self._summary(task))
        if isinstance(task, HigherUnaryObserve):
            self.ledger.bump("higher_unary_observations")
            return self._unary_apply(self.unary(task.summary), task.state)
        self.ledger.bump("higher_context_observations")
        return self._context_apply(
            self.context(task.summary), task.left, task.right, task.incoming, task.side
        )

    def _initial(self, task: HigherInitial) -> Generator[Task, Result, Result]:
        node = self.actions.node(task.action)
        arena = self.expressions
        if node.kind != "compose":
            value = (
                0
                if node.kind == "identity"
                else self.kernels.kernel(
                    self.kernels.intern(self.actions.primitive(task.action))
                ).initial(BoundarySide(task.side))
            )
            return arena.literal(self.boundaries.literal(task.action, task.side, value))
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        anchor = _expr((yield HigherInitial(first, task.side)))
        target = _expr((yield HigherInitial(second, task.side)))
        argument = arena.fresh_variable(
            arena.state_sort(first, 1 - task.side),
            "higher-initial-opposite",
            (anchor, target),
        )
        return arena.pair(
            task.action, task.side, anchor, arena.lambda_(argument, target)
        )

    def _reduce_continuation(self, function: ExprID) -> Generator[Task, Result, Result]:
        if (
            self.expressions.node(function).kind == "lambda"
            and self.expressions.constant_function(function) is None
        ):
            return (yield NormalizePrimitiveLambda(function))
        return function

    def _step(self, task: HigherStep) -> Generator[Task, Result, Result]:
        node, arena = self.actions.node(task.action), self.expressions
        if node.kind == "identity":
            return task.state
        if node.kind == "atom":
            if task.side == 1 and self.runtime.kernel(task.action).right_count == 1:
                self.ledger.bump("higher_singleton_right_steps")
                return task.state
            return arena.primitive_advance(
                task.action, task.side, task.state, task.symbol
            )
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        anchor, continuation = arena.anchor(task.state), arena.continuation(task.state)
        continuation = _expr((yield from self._reduce_continuation(continuation)))
        next_anchor = _expr((yield HigherStep(first, task.side, anchor, task.symbol)))
        argument = arena.fresh_variable(
            arena.state_sort(first, 1 - task.side),
            "higher-step-opposite",
            (task.state, task.symbol),
        )
        previous = arena.constant_function(continuation)
        if previous is None:
            opposite = _expr(
                (yield HigherStep(first, 1 - task.side, argument, task.symbol))
            )
            previous = arena.apply(continuation, opposite)
        else:
            self.ledger.bump("higher_constant_argument_elisions")
        left, right = (anchor, argument) if task.side == 0 else (argument, anchor)
        symbol = _expr((yield HigherEmit(first, left, task.symbol, right)))
        value = _expr((yield HigherStep(second, task.side, previous, symbol)))
        return arena.pair(
            task.action, task.side, next_anchor, arena.lambda_(argument, value)
        )

    def _emit(self, task: HigherEmit) -> Generator[Task, Result, Result]:
        node, arena = self.actions.node(task.action), self.expressions
        if node.kind == "identity":
            return task.symbol
        if node.kind == "atom":
            return arena.primitive_emit(task.action, task.left, task.symbol, task.right)
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        left, right = arena.anchor(task.left), arena.anchor(task.right)
        left_function, right_function = (
            arena.continuation(task.left),
            arena.continuation(task.right),
        )
        left_function = _expr((yield from self._reduce_continuation(left_function)))
        right_function = _expr((yield from self._reduce_continuation(right_function)))
        next_left, next_right = (
            arena.constant_function(left_function),
            arena.constant_function(right_function),
        )
        if next_left is None:
            left_argument = _expr((yield HigherStep(first, 1, right, task.symbol)))
            next_left = arena.apply(left_function, left_argument)
        else:
            self.ledger.bump("higher_constant_argument_elisions")
        if next_right is None:
            right_argument = _expr((yield HigherStep(first, 0, left, task.symbol)))
            next_right = arena.apply(right_function, right_argument)
        else:
            self.ledger.bump("higher_constant_argument_elisions")
        symbol = _expr((yield HigherEmit(first, left, task.symbol, right)))
        return _expr((yield HigherEmit(second, next_left, symbol, next_right)))

    def _right_reset(self, action: ActionProgramID, cell: CellID, side: int) -> bool:
        if side != 1:
            return False
        radius = self.runtime.resets.radius(action)
        return radius is not None and (
            radius == 0 or (radius - 1).bit_length() <= self.cells.node(cell).level
        )

    def _unary_summary(
        self, task: HigherUnarySummary
    ) -> Generator[Task, Result, Result]:
        node = self.cells.node(task.cell)
        variable = self._unary_variable(task.action, task.side)
        reset = self._right_reset(task.action, task.cell, task.side)
        if reset:
            variable = _expr((yield HigherInitial(task.action, task.side)))
            self.ledger.bump("higher_right_reset_specializations")
        temporal = self.actions.node(task.action)
        if temporal.kind == "compose":
            first, second = (
                self.actions.reference(temporal.first),
                self.actions.reference(temporal.second),
            )
            arena = self.expressions
            anchor, continuation = arena.anchor(variable), arena.continuation(variable)
            forward = self.unary(
                _summary_id((yield HigherUnarySummary(first, task.cell, task.side)))
            )
            context = self.context(
                _summary_id((yield HigherSummary(first, second, task.cell)))
            )
            argument = arena.fresh_variable(
                arena.state_sort(first, 1 - task.side),
                "higher-unary-opposite",
                (variable,),
            )
            incoming = arena.constant_function(continuation)
            if incoming is None:
                opposite = self.unary(
                    _summary_id(
                        (yield HigherUnarySummary(first, task.cell, 1 - task.side))
                    )
                )
                incoming = arena.apply(
                    continuation, self._unary_apply(opposite, argument)
                )
            else:
                self.ledger.bump("higher_constant_argument_elisions")
            left, right = (anchor, argument) if task.side == 0 else (argument, anchor)
            continuation_body = self._context_apply(
                context, left, right, incoming, task.side
            )
            body = arena.pair(
                task.action,
                task.side,
                self._unary_apply(forward, anchor),
                arena.lambda_(argument, continuation_body),
            )
            self.ledger.bump("higher_unary_temporal_compositions")
        elif temporal.kind == "atom":
            finite = _summary_id(
                (yield SpatialSummary(task.action, task.cell, task.side))
            )
            body = self.expressions.finite_apply(
                task.action, task.side, finite, variable
            )
            self.ledger.bump("higher_primitive_function_bindings")
        elif not node.level:
            symbol = self.expressions.symbol(
                task.action, self.cells.source_symbol(task.cell)
            )
            body = _expr((yield HigherStep(task.action, task.side, variable, symbol)))
            self.ledger.bump("higher_unary_leaf_compilations")
        else:
            low, high = self.cells.split(task.cell)
            before, after = (low, high) if task.side == 0 else (high, low)
            before_record = self.unary(
                _summary_id((yield HigherUnarySummary(task.action, before, task.side)))
            )
            after_record = self.unary(
                _summary_id((yield HigherUnarySummary(task.action, after, task.side)))
            )
            midpoint = self._unary_apply(before_record, variable)
            body = self._unary_apply(after_record, midpoint)
            self.ledger.bump("higher_unary_parent_compositions")
        program = self.expressions.closures.intern_canonical(
            (self._unary_variable(task.action, task.side),),
            body,
        )
        return self._publish_summary(
            task, HigherUnaryRecord(task.action, task.side, program)
        )

    def _summary(self, task: HigherSummary) -> Generator[Task, Result, Result]:
        node = self.cells.node(task.cell)
        left, right, incoming_left = self._context_variables(
            task.provider, task.consumer, 0
        )
        _, _, incoming_right = self._context_variables(task.provider, task.consumer, 1)
        if self._right_reset(task.consumer, task.cell, 1):
            incoming_right = _expr((yield HigherInitial(task.consumer, 1)))
            self.ledger.bump("higher_right_reset_specializations")
        if not node.level:
            original = self.expressions.symbol(
                task.provider, self.cells.source_symbol(task.cell)
            )
            symbol = _expr((yield HigherEmit(task.provider, left, original, right)))
            lbody = _expr((yield HigherStep(task.consumer, 0, incoming_left, symbol)))
            rbody = _expr((yield HigherStep(task.consumer, 1, incoming_right, symbol)))
            self.ledger.bump("higher_context_leaf_compilations")
        else:
            low_cell, high_cell = self.cells.split(task.cell)
            low = self.context(
                _summary_id(
                    (yield HigherSummary(task.provider, task.consumer, low_cell))
                )
            )
            high = self.context(
                _summary_id(
                    (yield HigherSummary(task.provider, task.consumer, high_cell))
                )
            )
            low_left = self.unary(
                _summary_id((yield HigherUnarySummary(task.provider, low_cell, 0)))
            )
            high_right = self.unary(
                _summary_id((yield HigherUnarySummary(task.provider, high_cell, 1)))
            )
            middle_left = self._unary_apply(low_left, left)
            middle_right = self._unary_apply(high_right, right)
            midpoint = self._context_apply(low, left, middle_right, incoming_left, 0)
            lbody = self._context_apply(high, middle_left, right, midpoint, 0)
            midpoint = self._context_apply(high, middle_left, right, incoming_right, 1)
            rbody = self._context_apply(low, left, middle_right, midpoint, 1)
            self.ledger.bump("higher_context_parent_compositions")
        left_program = self.expressions.closures.intern_canonical(
            self._context_variables(task.provider, task.consumer, 0),
            lbody,
        )
        right_program = self.expressions.closures.intern_canonical(
            self._context_variables(task.provider, task.consumer, 1),
            rbody,
        )
        return self._publish_summary(
            task,
            HigherContextRecord(
                task.provider, task.consumer, left_program, right_program
            ),
        )
