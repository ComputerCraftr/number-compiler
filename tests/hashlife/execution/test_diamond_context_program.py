"""Parent-first finite context programs never acquire future digit storage."""

from dataclasses import replace
from functools import partial
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import collatz_context_program_case
from tests.support.diamond_context_program import assert_context_inventory


def test_warm_context_parent_answers_with_all_child_and_primitive_evaluators_poisoned(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, _, contexts, request = collatz_context_program_case()
    expected = contexts.observations[request]
    before = runtime.ledger.snapshot()

    def forbidden(*args: object) -> Never:
        raise AssertionError("a warm parent evaluated a descendant")

    monkeypatch.setattr(contexts, "_substitute", forbidden)
    monkeypatch.setattr(runtime.kernels, "emit_expression", forbidden)
    monkeypatch.setattr(runtime.kernels, "advance_expression", forbidden)
    assert (
        contexts.execute(
            request.program, request.left, request.right, request.incoming, request.side
        )
        == expected
    )
    after = runtime.ledger.snapshot()
    assert after.entries == before.entries and after.nodes == before.nodes
    assert (
        after.counters["context_observation_cache_hits"]
        == before.counters.get("context_observation_cache_hits", 0) + 1
    )


def test_foreign_context_ports_reject_before_warm_lookup_or_mutation() -> None:
    runtime, _, contexts, request = collatz_context_program_case()
    _, _, _, other = collatz_context_program_case()
    for invalid in (
        replace(request, program=other.program),
        replace(request, incoming=other.incoming),
        replace(request, side=True),
    ):
        assert_rejected_atomically(
            runtime.ledger,
            partial(
                contexts.execute,
                invalid.program,
                invalid.left,
                invalid.right,
                invalid.incoming,
                invalid.side,
            ),
            (TypeError, ValueError),
        )


def test_context_node_and_interner_publication_is_atomic() -> None:
    runtime, action, contexts, request = collatz_context_program_case()
    parent = contexts.resolve(request.program)
    assert (
        parent.left is not None
        and parent.middle_left is not None
        and parent.middle_right is not None
    )
    left, middle_left, middle_right = (
        parent.left,
        parent.middle_left,
        parent.middle_right,
    )
    runtime.ledger.max_cache_entries = runtime.ledger.entries + 1
    assert_rejected_atomically(
        runtime.ledger,
        lambda: contexts.join(
            action,
            request.program,
            left,
            middle_left,
            middle_right,
        ),
        BlockContextBudgetExceeded,
    )


def test_actual_context_graph_and_unary_observations_are_accounted_independently() -> (
    None
):
    runtime, _, contexts, _ = collatz_context_program_case()
    report = collect_ledger_metrics(runtime.ledger)
    assert report.representation_boundary_complete == 1
    assert report.context_program_nodes == len(contexts._nodes)
    assert_context_inventory(contexts, report)
    assert report.resource_accounting_mismatch == 0
    registry = DiamondPayloadRegistry(runtime.ledger)
    assert all(registry.valid(node) for node in contexts._nodes)
    assert all(
        type(key) is ContextObservation and registry.valid(key)
        for key in contexts.observations
    )
    assert not registry.valid(replace(contexts._nodes[0], symbol=1 << 1000))
