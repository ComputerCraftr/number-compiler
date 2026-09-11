"""Domain proof metadata cannot authorize another mode or unsupported lambda."""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
    ExpressionAdmissionKey,
    ExpressionDomainProof,
)
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    CompileStructuredExpression,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.diamond_continuation_reduction import machine

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
        SemanticExpressionCompiler,
    )


def fixture(
    paired: bool = False,
) -> tuple[DiamondRuntime, SemanticExpressionCompiler, ExprID]:
    runtime, action = machine()
    if paired:
        action = runtime.actions.compose(action, action)
    expressions = runtime.higher.expressions
    variable = expressions.variable(expressions.state_sort(action, 0), "argument")
    body = expressions.anchor(variable) if paired else variable
    expression = expressions.lambda_(variable, body)
    compiler = runtime.semantic_compiler
    compiler.validate_task(CompileStructuredExpression(expression))
    return runtime, compiler, expression


@pytest.mark.parametrize("paired", (False, True))
def test_actual_domain_certificate_inventory_rechecks_supported_graph_without_execution(
    paired: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime, compiler, _ = fixture(paired)
    before = runtime.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "inventory trusted or replayed the producer domain validation"
        )

    monkeypatch.setattr(compiler, "_validate_domains", forbidden)
    monkeypatch.setattr(runtime, "execute", forbidden)
    report = collect_ledger_metrics(runtime.ledger)
    assert report.resource_audit_complete == 1 and report.forbidden_future_payloads == 0
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize(
    "mode", ("scalar-paired", "wrong-proof-key", "not-a-proof", "foreign-expression")
)
def test_actual_admission_bindings_do_not_attest_spoofed_modes_or_foreign_roots(
    mode: str,
) -> None:
    runtime, compiler, expression = fixture(True)
    key = ExpressionAdmissionKey(expression, False if mode == "scalar-paired" else True)
    proof: ExpressionDomainProof | ExprID = ExpressionDomainProof(key)
    if mode == "wrong-proof-key":
        proof = ExpressionDomainProof(ExpressionAdmissionKey(expression, False))
    elif mode == "not-a-proof":
        proof = expression
    elif mode == "foreign-expression":
        other, _, foreign = fixture()
        key = ExpressionAdmissionKey(foreign, True)
        proof = ExpressionDomainProof(key)
        assert other is not runtime
    if key not in compiler.admissions:
        runtime.ledger.reserve(compiler.admissions.owner, entries=1)
    cast(MutableMapping[object, object], compiler.admissions._data)[key] = proof
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0
    assert runtime.ledger.snapshot() == before
