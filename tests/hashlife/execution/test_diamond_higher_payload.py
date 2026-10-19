"""Higher transfer programs retain typed port functions and source bindings."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgram,
    ClosureProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_context import (
    HigherContextRecord,
    HigherUnaryRecord,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherEmit,
    HigherInitial,
    HigherSummary,
    HigherUnarySummary,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.diamond_boundary_expr import StateSort
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from tests.support.collatz_diamond_fixtures import collatz_higher_context_runtime
from tests.support.diamond_higher_context import expr, summary

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def populated() -> tuple[DiamondRuntime, ActionProgramID]:
    runtime, atom = collatz_higher_context_runtime()
    action = runtime.actions.compose(atom, atom)
    cell = runtime.cells.source(0, 2)
    summary(runtime, HigherSummary(action, atom, cell))
    summary(runtime, HigherUnarySummary(action, cell, 0))
    return runtime, action


def test_higher_program_metadata_and_bindings_are_independently_counted() -> None:
    runtime, _ = populated()
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert runtime.ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    carrier = runtime.higher
    assert report.boundary_expression_program_nodes == len(carrier.expressions.nodes)
    context_count = sum(type(node) is HigherContextRecord for node in carrier._nodes)
    unary_count = sum(type(node) is HigherUnaryRecord for node in carrier._nodes)
    assert context_count > 0 and unary_count > 0
    assert sum(len(node.free_ports) for node in carrier.expressions.nodes) > 0
    assert max(len(node.free_ports) for node in carrier.expressions.nodes) > 0
    assert report.spatial_action_program_nodes == len(carrier.expressions.nodes) + len(
        carrier._nodes
    ) + len(carrier.expressions.closures.nodes)
    assert report.macro_transfer_action_nodes == (
        len(carrier._nodes) + len(carrier.expressions.closures.nodes)
    )
    assert (
        sum(
            len(node.parameters) + len(node.support)
            for node in carrier.expressions.closures.nodes
        )
        > 0
    )
    assert (
        sum(
            len(node.children)
            for node in carrier.expressions.nodes
            if node.kind == "call"
        )
        > 0
    )
    inventory = {row.owner: row for row in report.resource_inventory}
    assert inventory[carrier.observations.owner].observed_entries == len(
        carrier.observations
    )
    assert report.spatial_occurrence_bindings >= len(carrier.bindings)
    registry = DiamondPayloadRegistry(runtime.ledger)
    assert all(registry.valid(record) for record in carrier._nodes)


def test_higher_program_cannot_add_an_unclaimed_free_port() -> None:
    runtime, action = populated()
    carrier, expressions = runtime.higher, runtime.higher.expressions
    unknown = expressions.variable(StateSort(action, 0), "unclaimed-carry-field")
    existing = next(
        record
        for record in carrier._nodes
        if type(record) is HigherUnaryRecord
        and record.action == action
        and record.side == 0
    )
    closures = expressions.closures
    record = replace(closures.resolve(existing.body), body=unknown, support=())
    runtime.ledger.reserve(closures.node_owner, entries=1, nodes=1)
    closures.nodes.append(record)
    bad = ClosureProgramID(
        closures.token, "diamond-expression-closure", len(closures.nodes) - 1
    )
    malformed = HigherUnaryRecord(action, 0, bad)
    runtime.ledger.reserve(carrier.node_owner, entries=1, nodes=1)
    carrier._nodes.append(malformed)
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0


def test_canonical_closure_audit_rejects_caller_selected_port_identity() -> None:
    runtime, action = populated()
    arena = runtime.higher.expressions
    parameter = arena.variable(StateSort(action, 0), "caller-selected-identity")
    record = ClosureProgram((parameter,), parameter, (parameter,))
    closures = arena.closures
    runtime.ledger.reserve(closures.node_owner, entries=1, nodes=1)
    closures.nodes.append(record)
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0


def test_higher_output_request_cannot_become_a_retained_observation_key() -> None:
    runtime, action = populated()
    left, right = (expr(runtime, HigherInitial(action, side)) for side in (0, 1))
    symbol = runtime.higher.expressions.symbol(action, 1)
    task = HigherEmit(action, left, symbol, right)
    owner = runtime.ledger.register("forbidden-output-cache", "query_memo")
    store: LedgerList[object]
    store = runtime.ledger.make_list(owner)
    runtime.ledger.reserve(owner, entries=1, nodes=1)
    store.append(task)
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0


def test_declared_free_port_summary_is_recomputed_from_actual_children() -> None:
    runtime, _ = populated()
    arena = runtime.higher.expressions
    node = next(node for node in arena.nodes if node.free_ports)
    malformed = replace(node, free_ports=())
    runtime.ledger.reserve(arena.node_owner, entries=1, nodes=1)
    arena.nodes.append(malformed)
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize(
    "failure",
    ("wrong-sort", "wrong-owner", "symbol-input", "closed-input", "closed-result"),
)
def test_resolved_head_memo_cannot_store_another_scope_sort_or_output_symbol(
    failure: str,
) -> None:
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        ResolveExpr,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        BoundaryExpressionArena,
    )

    runtime, action = collatz_higher_context_runtime()
    left = expr(runtime, HigherInitial(action, 0))
    right = expr(runtime, HigherInitial(action, 1))
    key, value = ResolveExpr(left), right
    if failure == "wrong-owner":
        other = BoundaryExpressionArena(runtime.boundaries)
        value = other.literal(runtime.boundaries.literal(action, 0, 0))
    elif failure == "symbol-input":
        value = runtime.higher.expressions.symbol(action, 0)
        key = ResolveExpr(value)
    elif failure == "closed-input":
        value = left
    elif failure == "closed-result":
        key = ResolveExpr(
            runtime.higher.expressions.variable(StateSort(action, 0), "open-carry")
        )
        value = left
    runtime.expression_heads[key] = value
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0


def test_open_function_head_normalization_is_audited_without_observing_its_ports() -> (
    None
):
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        ResolveExpr,
    )

    runtime, action = collatz_higher_context_runtime()
    arena = runtime.higher.expressions
    parameter = arena.variable(StateSort(action, 0), "parameter")
    incoming = arena.variable(StateSort(action, 0), "incoming")
    body = arena.primitive_advance(action, 0, parameter, arena.symbol(action, 2))
    closure = arena.closures.intern((parameter,), body)
    call = arena.call(closure, (incoming,))
    request = ResolveExpr(call)
    result = runtime.execute(request)
    assert runtime.expression_heads[request] == result
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert report.representation_boundary_complete == 1
    assert len(runtime.expression_heads) > 0
    expression_head_rows = tuple(
        row
        for row in report.resource_inventory
        if row.owner == runtime.expression_heads.owner
    )
    assert len(expression_head_rows) == 1
    assert expression_head_rows[0].observed_entries == len(runtime.expression_heads)
    assert runtime.ledger.snapshot() == before


def test_inventory_does_not_call_instrumented_higher_admission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, _ = populated()
    before = runtime.ledger.snapshot()

    def poison(*args: object, **kwargs: object) -> Never:
        raise AssertionError("inventory invoked production task admission")

    monkeypatch.setattr(type(runtime.higher), "validate", poison)
    monkeypatch.setattr(type(runtime.higher), "_validate", poison)
    report = collect_ledger_metrics(runtime.ledger)
    assert report.representation_boundary_complete == 1
    assert report.resource_accounting_mismatch == 0
    assert runtime.ledger.snapshot() == before
