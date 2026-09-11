"""Reset proof budgets reject before fixed-kernel work and permit warm reads."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from tests.support.diamond_primitive_step_reset import machine


@pytest.mark.parametrize("dimension", ("cache", "nodes"))
def test_exhausted_reset_proof_budget_preflights_before_kernel_work(
    dimension: str,
) -> None:
    runtime, action = machine()
    ledger = runtime.ledger
    if dimension == "cache":
        ledger.max_cache_entries = ledger.entries
    else:
        ledger.max_nodes = ledger.nodes
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        runtime.resets.radius(action)
    assert (ledger.entries, ledger.nodes, ledger.peak_entries, ledger.peak_nodes) == (
        before.entries,
        before.nodes,
        before.peak_entries,
        before.peak_nodes,
    )
    for counter in (
        "right_reset_primitive_checks",
        "primitive_transition_evaluations",
        "diamond_kernel_transition_evaluations",
        "bounded_limb_operations",
    ):
        assert ledger.counters.get(counter, 0) == before.counters.get(counter, 0)
    assert action not in runtime.resets.certificates


def test_warm_reset_certificate_needs_no_remaining_cache_or_node_space() -> None:
    runtime, action = machine()
    assert runtime.resets.radius(action) == 1
    ledger = runtime.ledger
    ledger.max_cache_entries = ledger.entries
    ledger.max_nodes = ledger.nodes
    before = ledger.snapshot()
    assert runtime.resets.radius(action) == 1
    assert (ledger.entries, ledger.nodes, ledger.peak_entries, ledger.peak_nodes) == (
        before.entries,
        before.nodes,
        before.peak_entries,
        before.peak_nodes,
    )
    assert ledger.counters.get(
        "right_reset_primitive_checks", 0
    ) == before.counters.get("right_reset_primitive_checks", 0)


def test_exception_during_proof_releases_its_reserved_entry_and_node(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = machine()
    ledger = runtime.ledger
    before = ledger.snapshot()

    def fail(_action: object) -> None:
        assert ledger.entries == before.entries + 1
        assert ledger.nodes == before.nodes + 1
        raise RuntimeError("injected proof failure")

    monkeypatch.setattr(runtime.resets, "_primitive_radius", fail)
    with pytest.raises(RuntimeError, match="injected proof failure"):
        runtime.resets.radius(action)
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
    assert action not in runtime.resets.certificates
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_successful_proof_has_one_actual_owner_and_one_charge() -> None:
    runtime, action = machine()
    ledger = runtime.ledger
    before = ledger.snapshot()
    assert runtime.resets.radius(action) == 1
    assert (ledger.entries, ledger.nodes) == (before.entries + 1, before.nodes + 1)
    account = next(
        row
        for row in ledger.inventory()
        if row.owner == runtime.resets.certificates.owner
    )
    assert (
        account.entries,
        account.nodes,
        account.observed_entries,
        account.observed_nodes,
    ) == (1, 1, 1, 1)
    assert all(row.accounting_delta == 0 for row in ledger.inventory())
