"""Independent ownership and free-port checks for higher K/U programs."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_payload import (
    ExpressionPayloadRegistry,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_context import (
    HigherContextArena,
    HigherContextRecord,
    HigherUnaryRecord,
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
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    StateSort,
    SymbolSort,
)
from number_compiler.resources.ledger import ResourceLedger


class HigherPayloadRegistry:
    record_types = (
        HigherContextRecord,
        HigherUnaryRecord,
        HigherInitial,
        HigherStep,
        HigherEmit,
        HigherSummary,
        HigherUnarySummary,
        HigherObserve,
        HigherUnaryObserve,
    )

    def __init__(
        self,
        ledger: ResourceLedger,
        expressions: ExpressionPayloadRegistry,
        action_valid: Callable[[object], bool],
    ) -> None:
        self.expressions, self.action_valid = expressions, action_valid
        actual = dict(ledger.iter_containers())
        self.arenas = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is HigherContextArena
            and root.ledger is ledger
            and root.expressions in expressions.arenas
            and actual.get(root.node_owner) is root._nodes
            and actual.get(root.id_owner) is root._ids
            and actual.get(root.binding_owner) is root.bindings
            and actual.get(root.observations.owner) is root.observations._data
        )
        self.records = {
            id(record): arena for arena in self.arenas for record in arena._nodes
        }
        self.invalid_response_objects: set[tuple[int, int]] = set()
        for arena in self.arenas:
            for key, result in arena.observations.items():
                if not self._observation(arena, key, result):
                    self.invalid_response_objects.update(
                        (
                            (arena.observations.owner, id(key)),
                            (arena.observations.owner, id(result)),
                        )
                    )

    def _task(self, arena: HigherContextArena, task: object) -> bool:
        """Independently inspect actual records; never invoke instrumented admission."""

        def action(value: ActionProgramID) -> bool:
            if (
                type(value) is not ActionProgramID
                or value.owner is not arena.actions.token
                or not self.action_valid(value)
            ):
                return False
            node = arena.actions._nodes[value.local_id]
            source = arena.cells.source_geometry._construction.source
            return node.kind == "identity" or (node.base, node.blank) == (
                source.base,
                source.blank,
            )

        def state(value: ExprID, owner: ActionProgramID, side: int) -> bool:
            if type(value) is not ExprID or value.owner is not arena.expressions.token:
                return False
            node = self.expressions.expression(value)
            return node is not None and node.sort == StateSort(owner, side)

        def symbol(value: ExprID) -> bool:
            if type(value) is not ExprID or value.owner is not arena.expressions.token:
                return False
            node = self.expressions.expression(value)
            source = arena.cells.source_geometry._construction.source
            return node is not None and node.sort == SymbolSort(
                source.base, source.blank
            )

        def source(cell: object) -> bool:
            from number_compiler.hashlife.actions.diamond_actions import CellID

            if type(cell) is not CellID:
                return False
            root = arena.cells.resolve(cell)
            pending, seen = [root], set()
            while pending:
                node = pending.pop()
                if id(node) in seen:
                    continue
                seen.add(id(node))
                if node.original_forward is not True:
                    return False
                if node.kind == "join":
                    for child in (node.left, node.right):
                        if type(child) is not int or not 0 <= child < len(
                            arena.cells._nodes
                        ):
                            return False
                        pending.append(arena.cells._nodes[child])
                elif node.kind != "source":
                    return False
            return True

        if type(task) in (HigherInitial, HigherStep, HigherUnarySummary) and isinstance(
            task, (HigherInitial, HigherStep, HigherUnarySummary)
        ):
            if (
                type(task.side) is not int
                or task.side not in (0, 1)
                or not action(task.action)
            ):
                return False
            if type(task) is HigherStep:
                return state(task.state, task.action, task.side) and symbol(task.symbol)
            return source(task.cell) if type(task) is HigherUnarySummary else True
        if type(task) is HigherSummary:
            return action(task.provider) and action(task.consumer) and source(task.cell)
        if type(task) is HigherObserve:
            if (
                type(task.side) is not int
                or task.side not in (0, 1)
                or not self.handle(task.summary)
                or task.summary.owner is not arena.token
            ):
                return False
            record = arena.context(task.summary)
            return (
                state(task.left, record.provider, 0)
                and state(task.right, record.provider, 1)
                and state(task.incoming, record.consumer, task.side)
            )
        if type(task) is HigherUnaryObserve:
            if not self.handle(task.summary) or task.summary.owner is not arena.token:
                return False
            unary = arena.unary(task.summary)
            return state(task.state, unary.action, unary.side)
        return False

    def _observation(
        self, arena: HigherContextArena, key: object, result: object
    ) -> bool:
        inputs: tuple[ExprID, ...] = ()
        try:
            if type(key) in (HigherInitial, HigherStep) and isinstance(
                key, (HigherInitial, HigherStep)
            ):
                if not self._task(arena, key):
                    return False
                expected = StateSort(key.action, key.side)
                if type(key) is HigherStep:
                    inputs = (key.state, key.symbol)
            elif type(key) is HigherObserve:
                if not self._task(arena, key):
                    return False
                record = arena.context(key.summary)
                expected = StateSort(record.consumer, key.side)
                inputs = (key.left, key.right, key.incoming)
            elif type(key) is HigherUnaryObserve:
                if not self._task(arena, key):
                    return False
                unary = arena.unary(key.summary)
                expected = StateSort(unary.action, unary.side)
                inputs = (key.state,)
            else:
                return False
        except (TypeError, ValueError, AttributeError, IndexError, KeyError):
            return False
        node = self.expressions.expression(result) if type(result) is ExprID else None
        return (
            node is not None
            and node.sort == expected
            and self.expressions.response_allowed(arena.expressions, result, inputs)
        )

    def handle(self, value: object) -> bool:
        if (
            type(value) is not TransferSummaryID
            or value.kind not in ("diamond-higher-context", "diamond-higher-unary")
            or type(value.local_id) is not int
            or value.local_id < 0
        ):
            return False
        for arena in self.arenas:
            if value.owner is arena.token and value.local_id < len(arena._nodes):
                record = arena._nodes[value.local_id]
                return (value.kind == "diamond-higher-context") == (
                    type(record) is HigherContextRecord
                ) and self._record(record)
        return False

    def _body(
        self,
        arena: HigherContextArena,
        program: ClosureProgramID,
        expected: StateSort,
        parameters: tuple[StateSort, ...],
    ) -> bool:
        record = self.expressions.closure(program, arena.expressions)
        if record is None:
            return False
        body = self.expressions.expression(record.body)
        return (
            body is not None
            and body.sort == expected
            and tuple(
                arena.expressions.nodes[parameter.local_id].sort
                for parameter in record.parameters
            )
            == parameters
        )

    def _record(self, value: object) -> bool:
        arena = self.records.get(id(value))
        if arena is None:
            return False
        if type(value) is HigherUnaryRecord:
            return (
                type(value.action) is ActionProgramID
                and self.action_valid(value.action)
                and value.action.owner is arena.actions.token
                and type(value.side) is int
                and value.side in (0, 1)
                and type(value.body) is ClosureProgramID
                and self._body(
                    arena,
                    value.body,
                    StateSort(value.action, value.side),
                    (StateSort(value.action, value.side),),
                )
            )
        if type(value) is HigherContextRecord:
            if not (
                type(value.provider) is ActionProgramID
                and type(value.consumer) is ActionProgramID
                and self.action_valid(value.provider)
                and self.action_valid(value.consumer)
                and value.provider.owner is value.consumer.owner is arena.actions.token
            ):
                return False
            return all(
                type(body) is ClosureProgramID
                and self._body(
                    arena,
                    body,
                    StateSort(value.consumer, side),
                    (
                        StateSort(value.provider, 0),
                        StateSort(value.provider, 1),
                        StateSort(value.consumer, side),
                    ),
                )
                for side, body in enumerate((value.left, value.right))
            )
        return False

    def valid(self, value: object) -> bool:
        if type(value) in (HigherContextRecord, HigherUnaryRecord):
            return self._record(value)
        if type(value) is HigherEmit:
            return False  # Output requests are transient; no response tape is admitted.
        if type(value) not in self.record_types:
            return False
        for arena in self.arenas:
            try:
                if isinstance(
                    value,
                    (
                        HigherInitial,
                        HigherStep,
                        HigherSummary,
                        HigherUnarySummary,
                        HigherObserve,
                        HigherUnaryObserve,
                    ),
                ) and self._task(arena, value):
                    return True
            except (TypeError, ValueError, AttributeError, IndexError, KeyError):
                continue
        return False
