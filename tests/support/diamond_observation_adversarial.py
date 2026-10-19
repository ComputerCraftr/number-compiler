"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from array import array

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprID,
    StateSort,
)
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.resources.ledger import ResourceLedger
from tests.support.diamond_query import build


def neighbor_xor() -> FiniteBlockEffect:
    # The right finite port copies exactly the most recent symbol. This is a
    # valid bounded reset function, but caching its observed result at every
    # future position would reconstruct the entire intermediate field.
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=4,
        alphabet_size=4,
        initial_left=0,
        initial_right=3,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [symbol for _ in range(4) for symbol in range(4)]),
        outputs=bytes(
            symbol ^ (right & 1) if symbol < 2 and right < 2 else symbol
            for symbol in range(4)
            for right in range(4)
        ),
        kernel_name="adversarial-neighbor-xor",
        storage_bytes=96,
        uncompressed_bytes=96,
        blank_left_tail=0,
        blank_right_tail=1,
        stable_blank_output=True,
    )


def bound_projection_fixture() -> tuple[
    ResourceLedger, BoundaryExpressionArena, ExprID, ExprID, ExprID, ExprID, ExprID
]:
    from tests.support.diamond_boundary_expr import context

    ledger, actions, boundaries, arena, first, _ = context()
    action = actions.compose(first, first)
    left = arena.literal(boundaries.literal(first, 0, 0))
    right = arena.literal(boundaries.literal(first, 1, 0))
    parameter = arena.variable(arena.state_sort(first, 0), "closure-argument")
    program = arena.closures.intern(
        (parameter,),
        arena.primitive_advance(first, 0, parameter, arena.symbol(first, 2)),
    )
    closed = arena.call(program, (left,))
    binder = arena.variable(arena.state_sort(first, 1), "continuation-argument")
    incoming = arena.pair(action, 0, left, arena.lambda_(binder, closed))
    variable = arena.variable(arena.state_sort(action, 0), "structured-parameter")
    projection = arena.anchor(variable)
    assert not arena.node(incoming).free_ports
    return ledger, arena, variable, incoming, projection, left, right


def structured_projection(
    arena: BoundaryExpressionArena,
    variable: ExprID,
    right: ExprID,
    expression: ExprID,
    expected: ExprID,
) -> tuple[ExprID, ExprID]:
    sort = arena.node(variable).sort
    assert type(sort) is StateSort
    parameter = arena.variable(arena.node(right).sort, "constant-continuation")
    continuation = arena.lambda_(parameter, expected)
    return arena.pair(sort.action, sort.side, expression, continuation), arena.pair(
        sort.action, sort.side, expected, continuation
    )


def bound_observation_fixture() -> tuple[
    DiamondApplication, DiamondRuntime, BoundaryExpressionArena, ActionProgramID, ExprID
]:
    app = build(neighbor_xor(), (0, 1, 1), 8, 1)
    runtime, arena = app.runtime, app.runtime.higher.expressions
    action = app.root
    literal = arena.literal(runtime.boundaries.literal(action, 1, 3))
    parameter = arena.variable(arena.state_sort(action, 1), "unresolved-input")
    body = arena.primitive_advance(action, 1, parameter, arena.symbol(action, 0))
    program = arena.closures.intern((parameter,), body)
    return app, runtime, arena, action, arena.call(program, (literal,))


def unsafe_capture(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    variable: ExprID,
    expression: ExprID,
) -> tuple[BoundaryExpressionArena, ExprID]:
    arena = runtime.higher.expressions
    literal = arena.literal(runtime.boundaries.literal(action, 0, 0))
    program = arena.closures.intern((variable,), expression)
    captured = arena.call(program, (literal,))
    right = arena.literal(runtime.boundaries.literal(action, 1, 0))
    symbol = arena.primitive_emit(action, captured, arena.symbol(action, 1), right)
    return arena, arena.primitive_advance(action, 0, variable, symbol)
