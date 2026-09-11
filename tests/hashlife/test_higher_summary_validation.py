from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    HigherSummaryID,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherFunctionID,
)
from tests.support.reverse_higher_interface import _direct_step
from tests.support.reverse_higher_runtime import _fixture


def test_higher_unary_summary_matches_primitive_spatial_transfer() -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    forest = sources.resolve_forest(binding)
    assert len(forest.cells) == 1
    summary = runtime.summaries.unary(primitive, forest.cells[0], 0)
    initial = runtime.initial(primitive, 0)
    observed = semantics.evaluate(runtime.summaries.apply_unary(summary, initial))
    expected = semantics.evaluate(
        runtime.boundary(primitive, binding, 0, 0, sources.binding_extent(binding))
    )
    assert observed == expected


def test_runtime_summary_ids_reject_foreign_aliases_before_publication() -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    _foreign_actions, foreign_primitive, _foreign_semantics, foreign_runtime, *_ = (
        _fixture((8,))
    )
    foreign_sources = foreign_runtime.sources.resolve_forest(
        foreign_runtime.sources.forest(0, 1)
    )
    foreign = foreign_runtime.summaries.runtime_unary(
        action=foreign_primitive,
        source=foreign_sources.cells[0],
        side=0,
    )
    before = len(semantics.runtime_values._records)
    with pytest.raises(ValueError, match="different arena"):
        semantics.runtime_values.transferred_state(foreign, 0)
    assert len(semantics.runtime_values._records) == before
    assert sources.binding_extent(binding) == 8


def test_higher_context_summary_composes_emitted_word_transfer() -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    forest = sources.resolve_forest(binding)
    assert len(forest.cells) == 1
    summary = runtime.summaries.context(primitive, primitive, forest.cells[0])
    initial_left = runtime.initial(primitive, 0)
    initial_right = runtime.initial(primitive, 1)
    observed = semantics.evaluate(
        runtime.summaries.apply_context(
            summary,
            initial_left,
            initial_right,
            initial_left,
            0,
        )
    )
    source = tuple(sources.binding_read(binding, index) for index in range(8))
    expected = semantics.schema.initial(primitive, 0)
    for symbol in _direct_step(source, 10):
        expected = semantics.schema.step(primitive, 0, expected, symbol)
    assert observed == expected


def test_higher_summary_semantics_survive_source_binding_eviction() -> None:
    (
        actions,
        primitive,
        _semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    forest = sources.resolve_forest(binding)
    assert len(forest.cells) == 1
    action = actions.power(primitive, 4)
    first = runtime.summaries.unary(action, forest.cells[0], 0)
    record = runtime.summaries.resolve(first)
    runtime.summaries.clear_bindings()
    second = runtime.summaries.unary(action, forest.cells[0], 0)
    assert second == first
    assert runtime.summaries.resolve(second) == record


def test_higher_summary_rejects_foreign_and_integer_alias_handles() -> None:
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    forest = sources.resolve_forest(binding)
    assert len(forest.cells) == 1
    valid = runtime.summaries.unary(primitive, forest.cells[0], 0)
    before = runtime.ledger.snapshot()
    aliases = (
        valid.local_id,
        True,
        0.0,
        HigherSummaryID(ArenaToken("foreign"), valid.kind, valid.local_id),
        HigherSummaryID(valid.owner, "higher-context-summary", valid.local_id),
        HigherSummaryID(valid.owner, valid.kind, valid.local_id + 1),
    )
    for alias in aliases:
        with pytest.raises((TypeError, ValueError)):
            runtime.summaries.resolve(alias)  # type: ignore[arg-type]
    after = runtime.ledger.snapshot()
    assert (after.entries, after.nodes, after.counters) == (
        before.entries,
        before.nodes,
        before.counters,
    )


def test_higher_summary_payload_audit_covers_nodes_bindings_and_eviction() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    (
        actions,
        primitive,
        _semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    cell = sources.resolve_forest(binding).cells[0]
    action = actions.power(primitive, 4)
    runtime.summaries.unary(action, cell, 0)
    runtime.summaries.context(primitive, primitive, cell)
    clean = audit_registered_payloads(runtime.ledger)
    assert clean.forbidden_future_payloads == 0
    assert clean.unknown_payloads == 0

    runtime.summaries.clear_bindings()
    evicted = audit_registered_payloads(runtime.ledger)
    assert evicted.forbidden_future_payloads == 0
    assert evicted.unknown_payloads == 0


def test_higher_summary_payload_audit_rejects_mutated_semantic_reference() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    cell = sources.resolve_forest(binding).cells[0]
    summary = runtime.summaries.unary(primitive, cell, 0)
    record = runtime.summaries.unary_record(summary)
    foreign = HigherFunctionID(
        ArenaToken("foreign"),
        record.function.kind,
        record.function.local_id,
    )
    runtime.summaries._nodes._data[summary.local_id] = replace(  # type: ignore[attr-defined]
        record,
        function=foreign,
    )
    damaged = audit_registered_payloads(runtime.ledger)
    assert damaged.forbidden_future_payloads > 0


def test_higher_summary_payload_audit_rejects_incompatible_binding_result() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _interfaces,
        _compiler,
        sources,
        binding,
    ) = _fixture()
    cell = sources.resolve_forest(binding).cells[0]
    left = runtime.summaries.unary(primitive, cell, 0)
    right = runtime.summaries.unary(primitive, cell, 1)
    key = next(
        key for key, result in runtime.summaries._bindings.items() if result == left
    )
    runtime.summaries._bindings._data[key] = right  # type: ignore[attr-defined]
    damaged = audit_registered_payloads(runtime.ledger)
    assert damaged.forbidden_future_payloads > 0
