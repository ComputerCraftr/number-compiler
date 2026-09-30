"""Cross-side primitive continuations preserve complete finite semantics."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    StateSort,
    BoundaryExpressionArena,
    ExprID,
)
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import input_expression
from tests.support.diamond_boundary_expr import context


def _check_cross_side_map(offset: int, *, metrics: bool) -> None:
    ledger, _, boundaries, arena, action, _ = context()
    primitive = arena.primitive(action)
    assert primitive is not None
    left, right = StateSort(action, 0), StateSort(action, 1)
    port = arena.variable(left, "incoming")
    assert primitive is not None
    forward = arena.unary._reduce(
        primitive.left_count,
        primitive.right_count,
        LEFT_A,
        lambda value: value % primitive.right_count,
    )
    assert primitive is not None
    backward = arena.unary._reduce(
        primitive.right_count,
        primitive.left_count,
        RIGHT_A,
        lambda value: 2 * value + offset,
    )
    assert primitive is not None
    expected = arena.unary._reduce(
        primitive.left_count,
        primitive.left_count,
        LEFT_A,
        lambda value: 2 * (value % primitive.right_count) + offset,
    )
    first = arena.finite_map(left, right, forward, port)
    composed = arena.finite_map(right, left, backward, first)
    assert arena.node(composed).children == (port.local_id,)
    assert arena.node(composed).function == expected
    # No continuation-state product: exactly one declared primitive input.
    assert primitive is not None
    for code in range(primitive.left_count):
        literal = arena.literal(boundaries.literal(action, 0, code))
        result = arena.substitute(composed, {port: literal})
        assert primitive is not None
        assert arena.node(result).value == 2 * (code % primitive.right_count) + offset
    if metrics:
        from number_compiler.resources.metric_collection import collect_ledger_metrics

        assert collect_ledger_metrics(ledger).representation_boundary_complete == 1


def test_cross_side_maps_compose_before_binding_their_argument() -> None:
    _check_cross_side_map(0, metrics=False)


def test_cross_action_constant_retains_target_sort_and_identity_retains_source() -> (
    None
):
    ledger, _, boundaries, arena, action, other = context()
    source, target = StateSort(action, 1), StateSort(other, 0)
    variable = arena.variable(source, "source")
    other_primitive = arena.primitive(other)
    action_primitive = arena.primitive(action)
    assert other_primitive is not None and action_primitive is not None
    constant = boundaries.kernels.constant(other_primitive.left_count, 2)
    result = arena.finite_map(source, target, constant, variable)
    assert arena.node(result).sort == target
    assert arena.node(result).value == 2
    identity = input_expression(
        boundaries.kernels, action_primitive.right_count, RIGHT_A
    )
    before = ledger.entries
    assert arena.finite_map(source, source, identity, variable) == variable
    assert ledger.entries == before


def test_cross_port_composition_normalizes_invalid_original_codes() -> None:
    _check_cross_side_map(1, metrics=True)


def _map_argument(
    arena: BoundaryExpressionArena, action: ActionProgramID
) -> tuple[StateSort, StateSort, ExprID, PrimitiveKernel]:
    source, target = StateSort(action, 1), StateSort(action, 0)
    variable = arena.variable(source, "x")
    primitive = arena.primitive(action)
    assert primitive is not None
    return source, target, variable, primitive


def test_foreign_map_argument_and_port_reject_before_warm_lookup_or_mutation() -> None:
    ledger, _, _boundaries, arena, action, _ = context()
    _, _, foreign_boundary, foreign, foreign_action, _ = context()
    source, target, x, primitive = _map_argument(arena, action)
    domain, codomain = (
        primitive.right_count,
        primitive.left_count,
    )
    function = arena.unary._reduce(domain, codomain, RIGHT_A, lambda code: code + 1)
    arena.finite_map(source, target, function, x)
    other_x = foreign.variable(StateSort(foreign_action, 1), "x")
    wrong_port = arena.unary._reduce(
        domain, codomain, PortVariable(0, 0, "foreign", 0), lambda code: code + 1
    )
    foreign_function = foreign_boundary.kernels.constant(codomain, 0)
    before = ledger.snapshot()
    for in_sort, out_sort, handle, argument in (
        (source, target, function, other_x),
        (StateSort(foreign_action, 1), target, function, x),
        (source, StateSort(foreign_action, 0), function, x),
        (source, target, foreign_function, x),
        (source, target, wrong_port, x),
    ):
        with pytest.raises(ValueError):
            arena.finite_map(in_sort, out_sort, handle, argument)
    assert ledger.snapshot() == before


def test_finite_map_node_and_identity_reservation_are_atomic() -> None:
    ledger, _, _, arena, action, _ = context()
    source, target, variable, primitive = _map_argument(arena, action)
    function = arena.unary._reduce(
        primitive.right_count,
        primitive.left_count,
        RIGHT_A,
        lambda code: code + 1,
    )
    before = ledger.snapshot()
    ledger.max_cache_entries = (
        before.entries + 1
    )  # A node without its key is not publishable.
    with pytest.raises(BlockContextBudgetExceeded):
        arena.finite_map(source, target, function, variable)
    after = ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
