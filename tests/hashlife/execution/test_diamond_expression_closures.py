"""Opaque program bodies preserve the binary DAG and explicit capture scope."""

import pytest

from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherInitial,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
)
from tests.support.diamond_higher_context import expr, machine, scalar


def test_closure_alpha_identity_and_unused_arguments_reduce_before_call_interning() -> (
    None
):
    runtime, action = machine()
    arena = runtime.higher.expressions
    sort = arena.state_sort(action, 0)
    first, unused = (
        arena.variable(sort, "first-name"),
        arena.variable(sort, "unused-name"),
    )
    renamed, renamed_unused = (
        arena.variable(sort, "renamed-first"),
        arena.variable(sort, "renamed-unused"),
    )
    symbol = arena.symbol(action, 1)
    body = arena.primitive_advance(action, 0, first, symbol)
    other_body = arena.primitive_advance(action, 0, renamed, symbol)
    one = arena.closures.intern((first, unused), body)
    two = arena.closures.intern((renamed, renamed_unused), other_body)
    assert one == two
    initial = expr(runtime, HigherInitial(action, 0))
    alternative = arena.literal(runtime.boundaries.literal(action, 0, 1))
    call = arena.call(one, (initial, initial))
    assert arena.call(one, (initial, alternative)) == call
    assert arena.node(call).children == (initial.local_id,)
    identity = arena.closures.intern((first, unused), first)
    assert arena.call(identity, (initial, alternative)) == initial


def test_call_and_outer_substitution_never_expand_a_program_body() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    sort = arena.state_sort(action, 0)
    formal, actual, replacement = (
        arena.variable(sort, name) for name in ("formal", "actual", "replacement")
    )
    symbol = arena.symbol(action, 1)
    body = formal
    for _ in range(16):
        body = arena.primitive_advance(action, 0, body, symbol)
    program = arena.closures.intern((formal,), body)
    before = sum(node.kind == "advance" for node in arena.nodes)
    call = arena.call(program, (actual,))
    substituted = arena.substitute(call, {actual: replacement})
    assert arena.node(substituted).closure == program
    assert arena.node(substituted).children == (replacement.local_id,)
    assert sum(node.kind == "advance" for node in arena.nodes) == before


def test_outer_lambda_cannot_capture_an_opaque_programs_formal_port() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    formal = arena.variable(arena.state_sort(action, 0), "original-formal")
    symbol = arena.symbol(action, 1)
    program = arena.closures.intern(
        (formal,), arena.primitive_advance(action, 0, formal, symbol)
    )
    initial = expr(runtime, HigherInitial(action, 0))
    call = arena.call(program, (initial,))
    hidden_formal = arena.closures.resolve(program).parameters[0]
    outer = arena.lambda_(hidden_formal, call)
    assert arena.constant_function(outer) == call
    alternate = arena.literal(runtime.boundaries.literal(action, 0, 1))
    assert arena.apply(outer, alternate) == call
    assert scalar(runtime, call) == scalar(
        runtime, arena.primitive_advance(action, 0, initial, symbol)
    )


def test_all_arguments_are_validated_even_when_program_ignores_them() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    formal = arena.variable(arena.state_sort(action, 0), "unused")
    initial = expr(runtime, HigherInitial(action, 0))
    program = arena.closures.intern((formal,), initial)
    assert arena.call(program, (initial,)) == initial
    foreign = BoundaryExpressionArena(runtime.boundaries)
    foreign_literal = foreign.literal(runtime.boundaries.literal(action, 0, 0))
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.call(program, (foreign_literal,))
    assert runtime.ledger.snapshot() == before


def test_undeclared_free_port_cannot_be_hidden_in_a_closure() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    allowed, hidden = (
        arena.variable(arena.state_sort(action, 0), name)
        for name in ("allowed", "hidden")
    )
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.closures.intern((allowed,), hidden)
    assert runtime.ledger.snapshot() == before


def test_closure_repeated_scalar_observation_has_no_output_response_index() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    formal = arena.variable(arena.state_sort(action, 0), "state")
    program = arena.closures.intern(
        (formal,), arena.primitive_advance(action, 0, formal, arena.symbol(action, 1))
    )
    call = arena.call(program, (expr(runtime, HigherInitial(action, 0)),))
    before = runtime.ledger.counters.get("boundary_expression_scalar_observations", 0)
    assert runtime.execute(LowerFinite(call)) == runtime.execute(LowerFinite(call))
    assert runtime.ledger.counters["boundary_expression_scalar_observations"] > before
