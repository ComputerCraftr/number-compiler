"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from array import array
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprID,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect


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


def _bound_projection_fixture() -> tuple[
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
