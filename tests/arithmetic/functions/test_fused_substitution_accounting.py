"""Independent accounting and exactness checks for fused finite-port substitution."""

from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
    from number_compiler.arithmetic.functions.finite_port_action import (
        FinitePortActionArena,
        PortVariable,
    )


def fixture() -> tuple[
    FinitePortActionArena,
    TransferSummaryID,
    dict[PortVariable, TransferSummaryID],
    tuple[PortVariable, PortVariable],
]:
    arena = FinitePortActionArena()
    px, py = PortVariable(0, 0, "carry", 0), PortVariable(1, 0, "carry", 0)
    x, y = arena.variable(px), arena.variable(py)
    root = arena.choose(x, y, arena.constant(False))
    replacements = {px: arena.negate(y), py: x}
    return arena, root, replacements, (px, py)


@pytest.mark.parametrize("available_entries", (0, 1))
def test_substitution_budget_rejection_publishes_no_partial_nodes_keys_or_cache(
    available_entries: int,
) -> None:
    arena, root, replacements, _ = fixture()
    before = arena.ledger.snapshot()
    original_nodes, original_keys = tuple(arena._nodes), dict(arena._keys)
    arena.ledger.tighten_limits(
        max_nodes=None, max_cache_entries=before.entries + available_entries
    )
    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute(root, replacements)
    after = arena.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert (after.peak_entries, after.peak_nodes) == (
        before.peak_entries,
        before.peak_nodes,
    )
    if available_entries:
        assert after.counters[
            "finite_port_substitution_staged_nodes"
        ] > before.counters.get("finite_port_substitution_staged_nodes", 0)
    assert tuple(arena._nodes) == original_nodes
    assert dict(arena._keys) == original_keys
    assert [(row.observed_entries, row.observed_nodes) for row in after.inventory] == [
        (row.observed_entries, row.observed_nodes) for row in before.inventory
    ]
    report = collect_ledger_metrics(arena.ledger)
    assert report.resource_accounting_mismatch == 0


def test_simultaneous_replacements_and_query_eviction_preserve_function_identity() -> (
    None
):
    arena, root, replacements, variables = fixture()
    before_nodes = len(arena._nodes)
    result = arena.substitute(root, replacements)
    for x, y in product((False, True), repeat=2):
        assert arena.apply(result, dict(zip(variables, (x, y), strict=True))) == (
            x and not y
        )
    final_nodes = len(arena._nodes)
    assert final_nodes >= before_nodes
    arena.ledger.evict_query_memos()
    assert arena.substitute(root, dict(reversed(tuple(replacements.items())))) == result
    assert len(arena._nodes) == final_nodes
    assert arena.retained_entries() == arena.ledger.entries
    report = collect_ledger_metrics(arena.ledger)
    assert report.resource_audit_complete == 1
    assert report.resource_accounting_mismatch == 0
    assert report.forbidden_future_payloads == 0


def test_effective_scoped_key_hits_before_reduction_and_ignores_unused_mapping_order() -> (
    None
):
    arena, root, replacements, _ = fixture()
    extra = PortVariable(2, 0, "unused", 0)
    extra_value = arena.variable(extra)
    expected = arena.substitute(root, replacements)
    before = arena.ledger.snapshot()
    reordered = dict(reversed(tuple(replacements.items())))
    reordered[extra] = extra_value
    assert arena.substitute(root, reordered) == expected
    after = arena.ledger.snapshot()
    assert (
        after.counters["finite_port_substitution_cache_hits"]
        == before.counters.get("finite_port_substitution_cache_hits", 0) + 1
    )
    for name in (
        "finite_port_substitution_evaluations",
        "finite_port_substitution_visits",
        "finite_port_substitution_support_visits",
        "finite_port_substitution_staged_nodes",
    ):
        assert after.counters.get(name, 0) == before.counters.get(name, 0)
    assert (after.nodes, after.entries) == (before.nodes, before.entries)
    assert len(arena._substitution.memo) == 1
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0


@pytest.mark.parametrize("foreign_kind", ("other-arena", "unallocated"))
def test_substitution_payload_audit_rejects_unowned_or_unallocated_component(
    foreign_kind: str,
) -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
    from number_compiler.arithmetic.functions.finite_port_action import PortComponent
    from number_compiler.arithmetic.functions.finite_port_substitution import (
        SubstitutionKey,
    )

    arena, root, replacements, _ = fixture()
    arena.substitute(root, replacements)
    bad_function = (
        FinitePortActionArena(arena.ledger).constant(False)
        if foreign_kind == "other-arena"
        else TransferSummaryID(
            arena.owner, "finite-port-function", len(arena._nodes) + 100
        )
    )
    variable = next(iter(replacements))
    malformed = SubstitutionKey(
        root, (PortComponent(variable, next(iter(replacements.values()))),)
    )
    object.__setattr__(
        malformed, "components", (PortComponent(variable, bad_function),)
    )
    owner = arena.ledger.register("malformed-substitution", "query_memo")
    storage: LedgerList[object]
    storage = arena.ledger.make_list(owner)
    arena.ledger.reserve(owner, entries=1, nodes=1)
    storage.append(malformed)
    before = arena.ledger.snapshot()
    report = collect_ledger_metrics(arena.ledger)
    assert arena.ledger.snapshot() == before
    assert report.forbidden_future_payloads > 0
    assert report.resource_accounting_mismatch == 0


def test_substitution_cache_uses_validated_private_integer_identities() -> None:
    arena, root, replacements, _ = fixture()
    expected = arena.substitute(root, replacements)
    key, result = next(iter(arena._substitution.memo.items()))
    assert type(key.function) is int
    assert all(type(component.function) is int for component in key.components)
    assert type(result) is int
    assert result == expected.local_id
    assert all(type(index) is int for index in arena._substitution.supports)
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0


def test_private_substitution_numeric_alias_corruption_is_audited() -> None:
    arena, root, replacements, _ = fixture()
    arena.substitute(root, replacements)
    key = next(iter(arena._substitution.memo))
    arena._substitution.memo[key] = True
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0


def test_substitution_request_units_separate_direct_results_hits_and_rejected_work() -> (
    None
):
    arena, root, replacements, variables = fixture()
    arena.substitute(root, {})
    arena.substitute(arena.constant(True), replacements)
    arena.substitute(root, {variables[0]: arena.constant(False)})
    arena.substitute(root, replacements)
    arena.substitute(root, replacements)
    counters = arena.ledger.counters
    assert counters["finite_port_substitution_direct_results"] == 3
    assert counters["finite_port_substitution_requests"] == sum(
        counters.get(name, 0)
        for name in (
            "finite_port_substitution_direct_results",
            "finite_port_substitution_cache_hits",
            "finite_port_substitution_evaluations",
            "finite_port_substitution_preflight_rejections",
        )
    )
    for available in (0, 1):
        rejected, function, mapping, _ = fixture()
        rejected.ledger.tighten_limits(None, rejected.ledger.entries + available)
        with pytest.raises(BlockContextBudgetExceeded):
            rejected.substitute(function, mapping)
        counts = rejected.ledger.counters
        assert counts["finite_port_substitution_requests"] == sum(
            counts.get(name, 0)
            for name in (
                "finite_port_substitution_direct_results",
                "finite_port_substitution_cache_hits",
                "finite_port_substitution_evaluations",
                "finite_port_substitution_preflight_rejections",
            )
        )
        assert (
            counts.get("finite_port_substitution_publication_rejections", 0)
            == available
        )
        assert counts.get("finite_port_substitution_evaluations", 0) == available
