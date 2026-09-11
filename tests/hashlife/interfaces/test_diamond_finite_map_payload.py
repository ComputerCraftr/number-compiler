"""Fixed primitive maps retain functions, with independently checked domains."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryActionArena
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprBinding,
    ExprID,
    ExprSubstitutionKey,
    StateSort,
)
from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import input_expression
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.diamond_boundary_expr import context


def mapped() -> tuple[
    ResourceLedger,
    BoundaryActionArena,
    BoundaryExpressionArena,
    ActionProgramID,
    StateSort,
    StateSort,
    ExprID,
]:
    ledger, _, boundaries, arena, action, _ = context()
    primitive = arena.primitive(action)
    assert primitive is not None
    source, target = StateSort(action, 1), StateSort(action, 0)
    kernels = boundaries.kernels
    argument = input_expression(kernels, primitive.right_count, RIGHT_A)
    bits = kernels.expression(argument).bits
    width = (primitive.left_count - 1).bit_length()
    function = kernels._intern_expression(
        FiniteExpression(
            primitive.left_count,
            bits + (kernels.functions.constant(False),) * (width - len(bits)),
        )
    )
    incoming = arena.variable(source, "fixed-right-port")
    result = arena.finite_map(source, target, function, incoming)
    assert arena.node(result).kind == "finite_map"
    return ledger, boundaries, arena, action, source, target, result


def test_cross_side_primitive_map_is_read_only_and_not_a_scalar_payload() -> None:
    ledger, _, _, _, _, _, _ = mapped()
    before = ledger.snapshot()
    assert collect_ledger_metrics(ledger).representation_boundary_complete == 1
    assert ledger.snapshot() == before


@pytest.mark.parametrize(
    "failure", ("wrong-port", "wrong-codomain", "wrong-input-sort")
)
def test_forged_map_record_cannot_change_its_actual_domain_contract(
    failure: str,
) -> None:
    ledger, boundaries, arena, action, source, target, result = mapped()
    node = arena.node(result)
    primitive = arena.primitive(action)
    assert primitive is not None
    if failure == "wrong-port":
        function = input_expression(boundaries.kernels, primitive.left_count, LEFT_A)
        malformed = replace(node, function=function)
    elif failure == "wrong-codomain":
        function = boundaries.kernels.constant(primitive.right_count, 0)
        malformed = replace(node, function=function)
    else:
        wrong = arena.variable(target, "wrong-input-sort")
        malformed = replace(
            node, children=(wrong.local_id,), free_ports=arena.node(wrong).free_ports
        )
    ledger.reserve(arena.node_owner, entries=1, nodes=1)
    arena.nodes.append(malformed)
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_map_on_universal_literal_input_is_allowed_as_a_finite_interface_key() -> None:
    ledger, boundaries, arena, action, source, target, result = mapped()
    function = arena.node(result).function
    assert function is not None
    literal = arena.literal(boundaries.literal(action, 1, 0))
    finite_input = arena.finite_map(source, target, function, literal)
    variable = arena.variable(target, "universal-target-port")
    target_literal = arena.literal(boundaries.literal(action, 0, 0))
    key = ExprSubstitutionKey(variable, (ExprBinding(variable, finite_input),))
    ledger.reserve(arena.memo_owner, entries=1)
    arena.memo[key] = target_literal
    before = ledger.snapshot()
    assert collect_ledger_metrics(ledger).representation_boundary_complete == 1
    assert ledger.snapshot() == before
