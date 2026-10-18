"""Higher transfer composition is checked independently of future fields."""

from __future__ import annotations

from functools import partial
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_context import (
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
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import Task
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryActionArena
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_higher_context import expr, machine, point, scalar, summary

if TYPE_CHECKING:
    import typing

    from number_compiler.hashlife.execution.continuations.diamond_context_program import (
        ContextObservation,
    )
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        LowerFinite,
        ResolveExpr,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Evaluate,
        Initial,
        Output,
        OutputFunction,
        PairSummary,
        ResetTransfer,
        SpatialSummary,
        Substitute,
        Transfer,
    )
    from number_compiler.hashlife.execution.diamond_continuation_reduction import (
        CompilePrimitiveFunction,
        NormalizePrimitiveLambda,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryStateID
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        CompileStructuredExpression,
        StructuredExpressionTask,
    )
    from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
        PrimitiveMacroKey,
        PrimitiveMacroObservation,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import StructureID


@pytest.mark.parametrize("steps", [0, 1, 2, 3, 4])
def test_composed_unary_context_matches_physical_integer_oracle(steps: int) -> None:
    runtime, primitive = machine()
    action = runtime.actions.power(primitive, steps)
    expected = 27
    for _ in range(steps):
        expected = expected // 2 if expected % 2 == 0 else 3 * expected + 1
    observed = [point(runtime, action, position) for position in range(8)]
    assert observed == [
        (expected >> position) & 1 if position < expected.bit_length() else 2
        for position in range(8)
    ]
    assert not any(isinstance(key, HigherEmit) for key in runtime.higher.observations)


@pytest.mark.parametrize("side", [0, 1])
def test_higher_provider_context_matches_complete_output_oracle(side: int) -> None:
    runtime, primitive = machine()
    provider = runtime.actions.power(primitive, 2)
    cell = runtime.cells.source(0, 3)
    compiled = summary(runtime, HigherSummary(provider, primitive, cell))
    left = expr(runtime, HigherInitial(provider, 0))
    right = expr(runtime, HigherInitial(provider, 1))
    incoming = expr(runtime, HigherInitial(primitive, side))
    observed = expr(runtime, HigherObserve(compiled, left, right, incoming, side))
    expected = runtime.kernel(primitive).initial(BoundarySide(side))
    word = [((41 >> i) & 1) if i < 6 else 2 for i in range(8)]
    for symbol in word if side == 0 else reversed(word):
        expected = runtime.kernel(primitive).advance(
            BoundarySide(side), expected, symbol
        )
    assert scalar(runtime, observed) == expected


def test_warm_parent_observation_never_reenters_source_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, primitive = machine()
    provider = runtime.actions.power(primitive, 2)
    cell = runtime.cells.source(0, 3)
    task = HigherSummary(provider, primitive, cell)
    compiled = summary(runtime, task)
    left = expr(runtime, HigherInitial(provider, 0))
    right = expr(runtime, HigherInitial(provider, 1))
    initial = expr(runtime, HigherInitial(primitive, 0))
    incoming = expr(
        runtime,
        HigherStep(
            primitive, 0, initial, runtime.higher.expressions.symbol(primitive, 1)
        ),
    )

    def forbidden(*args: object) -> Never:
        raise AssertionError("warm parent replayed source children")

    monkeypatch.setattr(runtime.higher, "_summary", forbidden)
    monkeypatch.setattr(runtime.higher, "_unary_summary", forbidden)
    monkeypatch.setattr(runtime.cells, "source_symbol", forbidden)
    assert summary(runtime, task) == compiled
    result = expr(runtime, HigherObserve(compiled, left, right, incoming, 0))
    assert scalar(runtime, result) in range(runtime.kernel(primitive).left_count)


def test_higher_admission_rejects_foreign_and_wrong_side_before_warm_mutation() -> None:
    runtime, primitive = machine()
    foreign, foreign_primitive = machine()
    initial = expr(runtime, HigherInitial(primitive, 0))
    foreign_initial = expr(foreign, HigherInitial(foreign_primitive, 0))
    task = HigherUnarySummary(primitive, runtime.cells.source(0, 3), 0)
    compiled = summary(runtime, task)
    bad = (
        HigherInitial(primitive, True),
        HigherUnaryObserve(compiled, foreign_initial),
        HigherUnarySummary(foreign_primitive, task.cell, 0),
        HigherUnaryObserve(
            TransferSummaryID(
                compiled.owner, "diamond-higher-context", compiled.local_id
            ),
            initial,
        ),
    )
    for request in bad:
        assert_rejected_atomically(
            runtime.ledger, partial(runtime.execute, request), (ValueError, TypeError)
        )


def test_summary_program_and_binding_reservations_are_atomic() -> None:
    runtime, primitive = machine()
    arena = runtime.higher
    variable = arena._unary_variable(primitive, 0)
    record = HigherUnaryRecord(
        primitive, 0, arena.expressions.closures.intern((variable,), variable)
    )
    key = HigherUnarySummary(primitive, runtime.cells.source(0, 3), 0)
    before = runtime.ledger.snapshot()
    runtime.ledger.max_cache_entries = before.entries + 2
    with pytest.raises(BlockContextBudgetExceeded):
        arena._publish_summary(key, record)
    assert runtime.ledger.snapshot() == before
    assert not arena._nodes and not arena._ids and not arena.bindings


def test_summary_records_reject_numeric_payload_disguises() -> None:
    _runtime, primitive = machine()
    with pytest.raises(ValueError):
        HigherUnaryRecord(primitive, 0, cast(ClosureProgramID, 123))
    with pytest.raises(ValueError):
        HigherContextRecord(
            primitive,
            primitive,
            cast(ClosureProgramID, 123),
            cast(ClosureProgramID, 456),
        )


@pytest.mark.parametrize("side", [0, 1])
@pytest.mark.parametrize("constant", [0, 1, None])
def test_complete_higher_step_matches_primitive_pair_for_every_argument(
    side: int, constant: None | int
) -> None:
    from number_compiler.hashlife.execution.continuations.diamond_tasks import Evaluate

    runtime, primitive, paired, arena, boundaries = _paired_fixture()
    kernel = runtime.kernel(primitive)
    domain = kernel.right_count if side == 0 else kernel.left_count
    anchor = boundaries.literal(primitive, side, 0)
    formal = arena.variable(
        arena.state_sort(primitive, 1 - side), "test-complete-opposite"
    )
    symbol = arena.symbol(primitive, 1)
    if constant is None:
        left = arena.literal(anchor) if side == 0 else formal
        right = formal if side == 0 else arena.literal(anchor)
        output = arena.primitive_emit(primitive, left, symbol, right)
        body = arena.primitive_advance(primitive, side, arena.literal(anchor), output)
    else:
        body = arena.literal(boundaries.literal(primitive, side, constant))
    function = arena.lambda_(formal, body)
    arguments = [
        boundaries.literal(primitive, 1 - side, value) for value in range(domain)
    ]
    values = [
        boundaries.literal(
            primitive,
            side,
            scalar(runtime, arena.apply(function, arena.literal(argument))),
        )
        for argument in arguments
    ]
    old_function = boundaries.finite_function(values, primitive, 1 - side)
    old_state = boundaries.pair(paired, side, anchor, old_function)
    expected = boundaries.state(
        runtime.primitive_pairs.advance(paired, old_state, side, 1)
    )
    assert expected.anchor is not None and expected.continuation is not None
    new_state = arena.pair(paired, side, arena.literal(anchor), function)
    actual = expr(runtime, HigherStep(paired, side, new_state, symbol))
    assert (
        scalar(runtime, arena.anchor(actual))
        == boundaries.state(expected.anchor).literal
    )
    actual_function = arena.continuation(actual)
    for argument in arguments:
        expected_value = runtime.execute(Evaluate(expected.continuation, argument))
        assert (
            scalar(runtime, arena.apply(actual_function, arena.literal(argument)))
            == boundaries.state(expected_value).literal
        )


def _paired_fixture() -> tuple[
    DiamondRuntime,
    ActionProgramID,
    ActionProgramID,
    BoundaryExpressionArena,
    BoundaryActionArena,
]:
    runtime, primitive = machine()
    return (
        runtime,
        primitive,
        runtime.actions.compose(primitive, primitive),
        runtime.higher.expressions,
        runtime.boundaries,
    )


def test_higher_step_binder_never_captures_an_incoming_same_named_free_port() -> None:
    runtime, primitive, paired, arena, boundaries = _paired_fixture()
    free = arena.variable(arena.state_sort(primitive, 1), "higher-step-opposite")
    argument = arena.variable(arena.state_sort(primitive, 1), "test-ignored-argument")
    anchor = arena.literal(boundaries.literal(primitive, 0, 0))
    symbol = arena.symbol(primitive, 1)
    body = arena.primitive_advance(
        primitive, 0, anchor, arena.primitive_emit(primitive, anchor, symbol, free)
    )
    state = arena.pair(paired, 0, anchor, arena.lambda_(argument, body))
    advanced = expr(runtime, HigherStep(paired, 0, state, symbol))
    for value in range(runtime.kernel(primitive).right_count):
        replacement = arena.literal(boundaries.literal(primitive, 1, value))
        before = arena.substitute(state, {free: replacement})
        expected = expr(runtime, HigherStep(paired, 0, before, symbol))
        after = arena.substitute(advanced, {free: replacement})
        assert after == expected


def test_complete_right_reset_specializes_before_opposite_transfer_dependency(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, primitive = machine()
    paired = runtime.actions.compose(primitive, primitive)
    cell = runtime.cells.source(0, 3)
    target = HigherUnarySummary(paired, cell, 1)
    forbidden = HigherUnarySummary(primitive, cell, 0)
    original = runtime._program
    observed = []

    def trace(
        task: Task,
    ) -> typing.Generator[
        Initial
        | Transfer
        | ResetTransfer
        | Substitute
        | Evaluate
        | Output
        | OutputFunction
        | PairSummary
        | SpatialSummary
        | ContextObservation
        | HigherInitial
        | HigherStep
        | HigherEmit
        | HigherSummary
        | HigherUnarySummary
        | HigherObserve
        | HigherUnaryObserve
        | LowerFinite
        | ResolveExpr
        | CompilePrimitiveFunction
        | NormalizePrimitiveLambda
        | CompileStructuredExpression
        | StructuredExpressionTask
        | PrimitiveMacroKey
        | PrimitiveMacroObservation,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
    ]:
        observed.append(task)
        assert task != forbidden, (
            "constant incoming continuation demanded its discarded opposite transfer"
        )
        return original(task)

    monkeypatch.setattr(runtime, "_program", trace)
    compiled = summary(runtime, target)
    assert runtime.ledger.counters["higher_right_reset_specializations"] > 0
    assert forbidden not in observed
    arena, boundaries = runtime.higher.expressions, runtime.boundaries
    formal = arena.variable(arena.state_sort(primitive, 0), "reset-arbitrary-input")
    outputs = set()
    for anchor_value in range(runtime.kernel(primitive).right_count):
        for function_value in range(runtime.kernel(primitive).right_count):
            anchor = arena.literal(boundaries.literal(primitive, 1, anchor_value))
            value = arena.literal(boundaries.literal(primitive, 1, function_value))
            state = arena.pair(paired, 1, anchor, arena.lambda_(formal, value))
            outputs.add(expr(runtime, HigherUnaryObserve(compiled, state)))
    assert len(outputs) == 1
