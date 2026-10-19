"""One original primitive port is quotiented extensionally, never a higher universe."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
)
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import collatz_continuation_runtime
from tests.support.diamond_continuation_reduction import (
    advance_after_emit,
    incoming_advance_task,
    literal,
    normalize,
)


@pytest.mark.parametrize("side", [0, 1])
def test_physical_four_zero_words_have_the_same_complete_function(side: int) -> None:
    runtime, action = collatz_continuation_runtime(PhysicalCollatzFourBlockEffect())
    arena = runtime.higher.expressions
    variable = arena.variable(arena.state_sort(action, side), "arbitrary-incoming")
    symbol = arena.symbol(action, 0)
    functions = []
    for length in (4, 8):
        body = variable
        for _ in range(length):
            body = arena.primitive_advance(action, side, body, symbol)
        functions.append(normalize(runtime, arena.lambda_(variable, body)))
    assert functions[0] == functions[1]
    kernel = runtime.kernel(action)
    for value in range(len(kernel.domain(BoundarySide(side)))):
        expected = value
        for _ in range(4):
            expected = kernel.advance(BoundarySide(side), expected, 0)
        applied = arena.apply(functions[0], literal(runtime, action, side, value))
        assert runtime.execute(LowerFinite(applied)) == expected
    assert runtime.ledger.counters["primitive_continuation_extensional_reductions"] >= 2


def test_cross_side_primitive_continuation_matches_every_input() -> None:
    runtime, action = collatz_continuation_runtime()
    arena = runtime.higher.expressions
    kernel = runtime.kernel(action)
    variable = arena.variable(arena.state_sort(action, 1), "opposite-input")
    left = literal(runtime, action, 0, kernel.initial(BoundarySide.LEFT))
    symbol = arena.symbol(action, 1)
    emitted = arena.primitive_emit(action, left, symbol, variable)
    body = arena.primitive_advance(action, 0, left, emitted)
    function = normalize(runtime, arena.lambda_(variable, body))
    for value in range(kernel.right_count):
        expected = kernel.advance(
            BoundarySide.LEFT,
            kernel.initial(BoundarySide.LEFT),
            kernel.emit(kernel.initial(BoundarySide.LEFT), 1, value),
        )
        actual = arena.apply(function, literal(runtime, action, 1, value))
        assert runtime.execute(LowerFinite(actual)) == expected


def test_closed_and_symbol_results_never_enter_function_binding_cache() -> None:
    runtime, action = collatz_continuation_runtime()
    arena = runtime.higher.expressions
    variable = arena.variable(arena.state_sort(action, 1), "input")
    left = literal(runtime, action, 0, 0)
    symbol = arena.symbol(action, 1)
    expressions = (left, symbol, arena.primitive_emit(action, left, symbol, variable))
    for expression in expressions:
        task = CompilePrimitiveFunction(variable, expression)
        runtime.execute(task)
        assert task not in runtime.primitive_continuations.maps


def test_extra_free_port_declines_normalization_and_foreign_input_is_atomic() -> None:
    runtime, action = collatz_continuation_runtime()
    arena = runtime.higher.expressions
    variable = arena.variable(arena.state_sort(action, 1), "input")
    other = arena.variable(arena.state_sort(action, 0), "other")
    _unused_symbol_binding, _unused_body_binding, function = advance_after_emit(
        arena, action, other, variable
    )
    assert normalize(runtime, function) == function
    assert (
        NormalizePrimitiveLambda(function)
        not in runtime.primitive_continuations.normalized
    )
    foreign, foreign_action = collatz_continuation_runtime()
    foreign_variable = foreign.higher.expressions.variable(
        foreign.higher.expressions.state_sort(foreign_action, 1), "input"
    )
    assert_rejected_atomically(
        runtime.ledger,
        lambda: runtime.execute(CompilePrimitiveFunction(foreign_variable, variable)),
        ValueError,
    )


def test_warm_complete_function_avoids_primitive_recomputation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = collatz_continuation_runtime()
    arena, task = incoming_advance_task(runtime, action)
    compiled = runtime.execute(task)
    assert task in runtime.primitive_continuations.maps

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm canonical function recompiled a primitive")

    monkeypatch.setattr(arena.unary, "mapped", forbidden)
    monkeypatch.setattr(runtime.kernels, "advance_expression", forbidden)
    assert runtime.execute(task) == compiled


def test_exhausted_function_binding_budget_fails_before_child_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    runtime, action = collatz_continuation_runtime()
    arena, task = incoming_advance_task(runtime, action)
    runtime.ledger.max_cache_entries = runtime.ledger.entries

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("an exhausted request reached primitive compilation")

    monkeypatch.setattr(arena.unary, "mapped", forbidden)
    before = runtime.ledger.entries
    with pytest.raises(BlockContextBudgetExceeded):
        runtime.execute(task)
    assert runtime.ledger.entries == before
    assert task not in runtime.primitive_continuations.maps


def test_foreign_publication_rejects_before_any_cache_or_counter_mutation() -> None:
    runtime, action = collatz_continuation_runtime()
    foreign, foreign_action = collatz_continuation_runtime()
    arena, task = incoming_advance_task(runtime, action)
    wrong = foreign.kernels.constant(runtime.kernel(action).left_count, 0)
    assert_rejected_atomically(
        runtime.ledger,
        lambda: runtime.primitive_continuations.publish(task, wrong),
        ValueError,
    )
    assert task not in runtime.primitive_continuations.maps
    function = arena.lambda_(task.variable, task.expression)
    other_arena = foreign.higher.expressions
    other_var = other_arena.variable(
        other_arena.state_sort(foreign_action, 0), "incoming"
    )
    other_fn = other_arena.lambda_(other_var, other_var)
    assert_rejected_atomically(
        runtime.ledger,
        lambda: runtime.primitive_continuations.publish(
            NormalizePrimitiveLambda(function), other_fn
        ),
        ValueError,
    )
