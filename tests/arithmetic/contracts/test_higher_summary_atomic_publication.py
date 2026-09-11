"""Atomic publication of higher semantic summaries and occurrence bindings."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    HigherSummaryArena,
)
from tests.support.reverse_higher_runtime import _fixture


def _populations(summaries: HigherSummaryArena) -> tuple[int, int, int, int]:
    return (
        len(summaries._nodes),
        len(summaries._keys),
        len(summaries._bindings),
        len(summaries._runtime_bindings),
    )


def _owned_counts(summaries: HigherSummaryArena) -> tuple[tuple[int, int], ...]:
    inventory = summaries.ledger.snapshot().inventory
    return tuple(
        (inventory[owner].entries, inventory[owner].nodes)
        for owner in (
            summaries._node_owner,
            summaries._key_owner,
            summaries._binding_owner,
            summaries._runtime_binding_owner,
        )
    )


def test_runtime_summary_binding_capacity_is_reserved_before_semantic_node() -> None:
    _, primitive, semantics, runtime, _, _, sources, _ = _fixture((7,))
    summaries = runtime.summaries
    source = sources.intern(0, 0)
    symbol = sources.symbol(source)
    for state in range(semantics.schema.state_count(primitive, 0)):
        semantics.primitive_tables.step(primitive, 0, state, symbol)
    before = semantics.ledger.snapshot()
    populations = _populations(summaries)
    owned = _owned_counts(summaries)
    semantics.ledger.max_cache_entries = before.entries + 2

    with pytest.raises(BlockContextBudgetExceeded):
        summaries.runtime_unary(primitive, source, 0)

    after = semantics.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert _populations(summaries) == populations
    assert _owned_counts(summaries) == owned


def test_syntax_summary_cannot_publish_without_its_reserved_binding() -> None:
    (
        _,
        probe_action,
        probe_semantics,
        probe_runtime,
        _,
        _,
        probe_sources,
        probe_forest,
    ) = _fixture((7,))
    probe_source = probe_sources.resolve_forest(probe_forest).cells[0]
    probe_before = probe_semantics.ledger.snapshot().entries
    probe_runtime.summaries.unary(probe_action, probe_source, 0)
    request_entries = probe_semantics.ledger.snapshot().entries - probe_before
    assert request_entries >= 3

    _, primitive, semantics, runtime, _, _, sources, forest = _fixture((7,))
    summaries = runtime.summaries
    source = sources.resolve_forest(forest).cells[0]
    before = semantics.ledger.snapshot()
    populations = _populations(summaries)
    owned = _owned_counts(summaries)
    semantics.ledger.max_cache_entries = before.entries + request_entries - 1

    with pytest.raises(BlockContextBudgetExceeded):
        summaries.unary(primitive, source, 0)

    # Canonical expression children constructed before exhaustion may remain useful,
    # but the rejected summary node, its key, and its binding publish as one unit.
    assert _populations(summaries) == populations
    assert _owned_counts(summaries) == owned
