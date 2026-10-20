"""Only domain-validation proofs are cached; observations remain uncached."""

from __future__ import annotations

from dataclasses import fields
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
    ExpressionAdmissionKey,
)
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    CompileStructuredExpression,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import collatz_continuation_runtime

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def request() -> tuple[DiamondRuntime, ActionProgramID, CompileStructuredExpression]:
    runtime, action = collatz_continuation_runtime()
    arena = runtime.higher.expressions
    variable = arena.variable(arena.state_sort(action, 0), "argument")
    body = variable
    for _ in range(12):
        body = arena.primitive_advance(action, 0, body, arena.symbol(action, 1))
    return runtime, action, CompileStructuredExpression(arena.lambda_(variable, body))


def test_warm_parent_domain_proof_skips_descendants_and_domain_evaluators(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, _, task = request()
    compiler = runtime.semantic_compiler
    compiler.validate_task(task)
    before = runtime.ledger.counters["semantic_expression_admission_frames"]

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("warm admission replayed a descendant or lambda domain")

    monkeypatch.setattr(compiler, "_validate_domains", forbidden)
    monkeypatch.setattr(compiler, "input_ports", forbidden)
    monkeypatch.setattr(compiler, "atom_sort", forbidden)
    for _ in range(5):
        assert compiler.probe_task(task) is None
    assert runtime.ledger.counters["semantic_expression_admission_frames"] == before
    assert runtime.ledger.counters["semantic_expression_admission_hits"] == 5
    assert len(compiler.admissions) == 1


@pytest.mark.parametrize(
    "field,value",
    [("local_id", True), ("local_id", 0.0), ("local_id", -1), ("kind", "other")],
)
def test_forged_root_is_rejected_before_admission_proof_lookup(
    monkeypatch: pytest.MonkeyPatch, field: str, value: bool | float | str
) -> None:
    runtime, _, task = request()
    compiler = runtime.semantic_compiler
    compiler.validate_task(task)
    forged = object.__new__(type(task.expression))
    for item in fields(task.expression):
        object.__setattr__(
            forged,
            item.name,
            value if item.name == field else getattr(task.expression, item.name),
        )

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("invalid root reached the proof lookup")

    monkeypatch.setattr(compiler.admissions, "get", forbidden)
    assert_rejected_atomically(
        runtime.ledger,
        lambda: compiler.validate_task(CompileStructuredExpression(forged)),
        ValueError,
    )


def test_foreign_parameter_and_undeclared_parameter_reject_before_warm_hit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = collatz_continuation_runtime()
    arena, compiler = runtime.higher.expressions, runtime.semantic_compiler
    local = arena.variable(arena.state_sort(action, 0), "free")
    task = CompileStructuredExpression(local, (local,))
    compiler.validate_task(task)
    other, other_action = collatz_continuation_runtime()
    foreign = other.higher.expressions.variable(
        other.higher.expressions.state_sort(other_action, 0), "free"
    )

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("invalid parameter reached the proof lookup")

    monkeypatch.setattr(compiler.admissions, "get", forbidden)
    before = runtime.ledger.snapshot()
    for parameters in ((foreign,), ()):
        with pytest.raises(ValueError):
            compiler.validate_task(CompileStructuredExpression(local, parameters))
    assert runtime.ledger.snapshot() == before


def test_structured_proof_does_not_admit_a_scalar_only_compilation() -> None:
    runtime, action = collatz_continuation_runtime()
    arena, compiler = runtime.higher.expressions, runtime.semantic_compiler
    paired = runtime.actions.compose(action, action)
    variable = arena.variable(arena.state_sort(paired, 0), "paired-domain")
    function = arena.lambda_(variable, arena.anchor(variable))
    compiler.validate_task(CompileStructuredExpression(function))
    assert_rejected_atomically(
        runtime.ledger,
        lambda: compiler.compile(function),
        UnsupportedInterfaceError,
        match="composed input",
    )
    assert list(compiler.admissions) == [ExpressionAdmissionKey(function, True)]


def test_proof_eviction_releases_slots_and_revalidates_without_changing_ids() -> None:
    runtime, _, task = request()
    compiler = runtime.semantic_compiler
    compiler.validate_task(task)
    frames = runtime.ledger.counters["semantic_expression_admission_frames"]
    proof = compiler.admissions[ExpressionAdmissionKey(task.expression, True)]
    runtime.ledger.evict_query_memos()
    assert not compiler.admissions
    compiler.validate_task(task)
    assert runtime.ledger.counters["semantic_expression_admission_frames"] == 2 * frames
    assert compiler.admissions[proof.key] == proof
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())


def test_proof_publication_failure_keeps_retained_inventory_atomic() -> None:
    runtime, _, task = request()
    before = runtime.ledger.snapshot()
    runtime.ledger.tighten_limits(None, before.entries)
    with pytest.raises(BlockContextBudgetExceeded):
        runtime.semantic_compiler.validate_task(task)
    after = runtime.ledger.snapshot()
    assert (
        after.entries,
        after.nodes,
        after.inventory,
        after.peak_entries,
        after.peak_nodes,
    ) == (
        before.entries,
        before.nodes,
        before.inventory,
        before.peak_entries,
        before.peak_nodes,
    )
    assert not runtime.semantic_compiler.admissions
