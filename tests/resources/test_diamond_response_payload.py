"""Inspect memo bindings independently of the production publication guard."""

import pytest

from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherUnaryObserve,
    HigherUnarySummary,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprBinding,
    ExprSubstitutionKey,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.diamond_observation_adversarial import (
    _bound_projection_fixture,
    bound_observation_fixture,
    structured_projection,
    unsafe_capture,
)


@pytest.mark.parametrize("structured", (False, True))
def test_injected_bound_substitution_response_fails_independent_inventory(
    structured: bool,
) -> None:
    ledger, arena, variable, incoming, projection, literal, right = (
        _bound_projection_fixture()
    )
    result = literal
    if structured:
        projection, result = structured_projection(
            arena, variable, right, projection, result
        )
    assert collect_ledger_metrics(ledger).representation_boundary_complete == 1
    key = ExprSubstitutionKey(projection, (ExprBinding(variable, incoming),))
    ledger.reserve(arena.memo_owner, entries=1)
    arena.memo[key] = result
    before = ledger.snapshot()
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads >= 2
    assert report.resource_accounting_mismatch == 0
    assert ledger.snapshot() == before


def test_injected_higher_bound_observation_response_fails_independent_inventory() -> (
    None
):
    _app, runtime, _unused_arena_binding, action, incoming = bound_observation_fixture()
    summary = runtime.execute(HigherUnarySummary(action, runtime.cells.source(0, 1), 1))
    request = HigherUnaryObserve(summary, incoming)
    result = runtime.execute(request)
    assert request not in runtime.higher.observations
    assert collect_ledger_metrics(runtime.ledger).representation_boundary_complete == 1
    runtime.higher.observations[request] = result
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert report.forbidden_future_payloads >= 2
    assert report.resource_accounting_mismatch == 0
    assert runtime.ledger.snapshot() == before


def test_universal_finite_identity_on_a_literal_port_remains_valid() -> None:
    ledger, arena, _, _, _, literal, _ = _bound_projection_fixture()
    parameter = arena.variable(arena.node(literal).sort, "universal-finite-input")
    key = ExprSubstitutionKey(parameter, (ExprBinding(parameter, literal),))
    ledger.reserve(arena.memo_owner, entries=1)
    arena.memo[key] = literal
    before = ledger.snapshot()
    assert collect_ledger_metrics(ledger).representation_boundary_complete == 1
    assert ledger.snapshot() == before


@pytest.mark.parametrize("store", ("expression", "higher"))
def test_open_unsafe_input_cannot_acquire_a_safe_program_response_binding(
    store: str,
) -> None:
    from tests.support.diamond_continuation_payload import populated

    runtime, action, variable, expression, _, _ = populated()
    arena, unsafe = unsafe_capture(runtime, action, variable, expression)
    assert arena.node(unsafe).free_ports and not arena.node(unsafe).binding_safe
    assert arena.node(variable).binding_safe
    if store == "expression":
        parameter = arena.variable(arena.node(variable).sort, "response-parameter")
        key = ExprSubstitutionKey(parameter, (ExprBinding(parameter, unsafe),))
        runtime.ledger.reserve(arena.memo_owner, entries=1)
        arena.memo[key] = variable
    else:
        summary = runtime.execute(
            HigherUnarySummary(action, runtime.cells.source(0, 1), 0)
        )
        runtime.higher.observations[HigherUnaryObserve(summary, unsafe)] = variable
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads >= 2
    assert runtime.ledger.snapshot() == before
