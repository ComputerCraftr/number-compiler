"""Finite function reductions keep a live interface, not bound observations."""

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    StateSort,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.diamond_continuation_payload import populated


def test_actual_primitive_function_map_has_a_live_domain_and_read_only_inventory() -> (
    None
):
    runtime, _, _, _, _, _ = populated()
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert report.representation_boundary_complete == 1
    assert report.resource_work_counters["primitive_continuation_evaluations"] > 0
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize(
    "failure", ("closed-key", "symbol-output", "foreign-port", "wrong-codomain")
)
def test_injected_reduction_binding_cannot_hide_bound_values_or_change_domains(
    failure: str,
) -> None:
    runtime, action, variable, _, key, function = populated()
    arena = runtime.higher.expressions
    if failure == "closed-key":
        closed = arena.literal(runtime.boundaries.literal(action, 0, 0))
        key = replace(key, expression=closed)
    elif failure == "symbol-output":
        right = arena.literal(runtime.boundaries.literal(action, 1, 0))
        output = arena.primitive_emit(action, variable, arena.symbol(action, 1), right)
        key = replace(key, expression=output)
        function = runtime.execute(key)
        assert key not in runtime.primitive_continuations.maps
    elif failure == "foreign-port":
        other = BoundaryExpressionArena(runtime.boundaries)
        key = replace(
            key, variable=other.variable(StateSort(action, 0), "primitive-input")
        )
    else:
        function = runtime.kernels.constant(100, 0)
    runtime.primitive_continuations.maps[key] = function
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads >= 2
    assert runtime.ledger.snapshot() == before


def test_constant_finite_function_is_not_misclassified_as_a_scalar_observation() -> (
    None
):
    runtime, _, _, _, key, _ = populated()
    existing = runtime.primitive_continuations.maps[key]
    domain = runtime.kernels.expression(existing).domain
    runtime.primitive_continuations.maps[key] = runtime.kernels.constant(domain, 0)
    assert collect_ledger_metrics(runtime.ledger).representation_boundary_complete == 1


def test_normalization_cannot_bind_closed_function_program_to_realized_response() -> (
    None
):
    runtime, action, variable, expression, _, _ = populated()
    arena = runtime.higher.expressions
    function = arena.lambda_(variable, expression)
    literal = arena.literal(runtime.boundaries.literal(action, 0, 0))
    realized = arena.lambda_(variable, literal)
    runtime.primitive_continuations.normalized[NormalizePrimitiveLambda(function)] = (
        realized
    )
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads >= 2
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize("opaque", (False, True))
def test_live_input_cannot_hide_closed_capture_in_children_or_opaque_closure_body(
    opaque: bool,
) -> None:
    runtime, action, variable, expression, _, function = populated()
    arena = runtime.higher.expressions
    literal = arena.literal(runtime.boundaries.literal(action, 0, 0))
    captured_program = arena.closures.intern((variable,), expression)
    captured = arena.call(captured_program, (literal,))
    right = arena.literal(runtime.boundaries.literal(action, 1, 0))
    captured_symbol = arena.primitive_emit(
        action, captured, arena.symbol(action, 1), right
    )
    body = arena.primitive_advance(action, 0, variable, captured_symbol)
    if opaque:
        program = arena.closures.intern((variable,), body)
        body = arena.call(program, (variable,))
        assert arena.node(body).children == (variable.local_id,)
    assert arena.node(body).free_ports == arena.node(variable).free_ports
    assert collect_ledger_metrics(runtime.ledger).representation_boundary_complete == 1
    runtime.primitive_continuations.maps[CompilePrimitiveFunction(variable, body)] = (
        function
    )
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads >= 2
    assert runtime.ledger.snapshot() == before
