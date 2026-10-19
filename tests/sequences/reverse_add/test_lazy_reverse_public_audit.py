from typing import Never

import pytest

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.reverse_cutover import (
    assert_q19_application_counts_unchanged,
    assert_q19_output_authority,
    q19_application_counts,
)


def reference(seed: int, generations: int) -> int:
    for _ in range(generations):
        seed += int(str(seed)[::-1])
    return seed


@pytest.mark.validation  # N=64 multi-coordinate, width and independent payload audit.
def test_public_reverse_point_has_no_exact_future_carrier_or_global_offset_cache(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("point query reached a whole-field/slab lowering path")

    monkeypatch.setattr(ReverseAddPoweredTerm, "digits", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    term = ReverseAddPoweredTerm(196, 64)
    expected = str(reference(196, 64))
    assert term.digit(0) == int(expected[-1])
    assert term.width() == len(expected)
    for position in (3, len(expected) // 2, len(expected) - 1):
        assert term.digit(position) == int(expected[-1 - position])
    with pytest.raises(IndexError):
        term.digit(len(expected))
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
    metrics = term.metrics()
    assert metrics.forbidden_future_payloads == 0
    assert metrics.retained_unbounded_future_integers == 0
    assert metrics.resource_audit_unknown_payloads == 0
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.exact_endpoint_nodes == 0
    assert metrics.lowering_cache_entries == 0
    # Each spatial parent can need at most two carry-band representatives for
    # each of its two activity predicates.  The old implementation decoded
    # all 43 decimal left states for both predicates.
    assert metrics.reverse_port_predicate_state_evaluations <= (
        4 * metrics.reverse_port_parent_interfaces
    )


def test_unrelated_public_reverse_query_cannot_change_existing_inventory_or_work() -> (
    None
):
    first = ReverseAddPoweredTerm(196, 32)
    first.digit(0)
    before = first.metrics()
    second = ReverseAddPoweredTerm(89, 16)
    second.digit(0)
    after = first.metrics()
    assert after.point_queries == before.point_queries
    assert after.resource_ledger_entries == before.resource_ledger_entries
    assert after.resource_ledger_nodes == before.resource_ledger_nodes
    assert after.resource_inventory == before.resource_inventory
    assert (
        after.bounded_application_query_requests
        == before.bounded_application_query_requests
    )


def test_public_reverse_summary_eviction_preserves_result_and_program_identity() -> (
    None
):
    term = ReverseAddPoweredTerm(196, 32)
    expected = term.digit(3)
    before = term.metrics()
    workspace, occurrence = assert_q19_output_authority(term)
    q19_applications = q19_application_counts(term.resource_ledger.counters)
    q19_t2, q19_t4, q19_primitive_steps = q19_applications
    q19_visits = term.resource_ledger.counters.get(
        "reverse_q19_pair_output_nodes_visited", 0
    )
    assert 2 * q19_t2 + 4 * q19_t4 + q19_primitive_steps > 0
    assert q19_visits > 0
    term.resource_ledger.evict_query_memos()
    assert term.digit(3) == expected
    after = term.metrics()
    assert after.action_program_nodes == before.action_program_nodes
    # Query summaries are evictable, while the authenticated Q19 occurrence
    # remains the output authority. Re-answering it must not reapply a pair step.
    assert (
        after.bounded_application_nonlinear_branch_evaluations
        == before.bounded_application_nonlinear_branch_evaluations
    )
    counters = term.resource_ledger.counters
    retained_workspace, retained_occurrence = assert_q19_output_authority(term)
    assert retained_workspace is workspace
    assert retained_occurrence == occurrence
    assert_q19_application_counts_unchanged(counters, q19_applications)
    assert counters.get("reverse_q19_pair_output_nodes_visited", 0) == q19_visits
    assert after.temporal_parent_compositions == before.temporal_parent_compositions
    assert after.resource_accounting_mismatch == 0
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
    assert term.metrics().resource_audit_complete == 1
