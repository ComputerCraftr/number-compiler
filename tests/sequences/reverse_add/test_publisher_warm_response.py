"""Source-image reuse evidence for the canonical 196 reverse/add runtime."""

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_public_196_point_reuses_authenticated_scalar_without_replaying_image() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    position = term.maximum_width // 3
    expected = term.digit(position)
    before = dict(term._ledger.counters)
    assert term.digit(position) == expected
    after = term._ledger.counters

    assert (
        after.get("source_image_projection_requests", 0)
        - before.get("source_image_projection_requests", 0)
        == 1
    )
    assert (
        after.get("source_image_projection_hits", 0)
        - before.get("source_image_projection_hits", 0)
        == 1
    )
    # The cached projection is reused without reconstructing the recursive
    # occurrence or applying another temporal provider.
    for counter in (
        "source_image_projection_evaluations",
        "reverse_source_recursive_occurrence_publications",
        "reverse_source_completed_child_publications",
        "reverse_recursive_provider_applications",
        "reverse_recursive_completed_child_joins",
        "reverse_provider_parent_substitutions",
        "higher_action_continuation_requests",
        "higher_concrete_operation_evaluations",
        "sequential_generation_advances",
        "source_image_primitive_applications",
    ):
        assert after.get(counter, 0) - before.get(counter, 0) == 0


def test_cold_196_point_reports_published_runtime_image_work() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    expected = 196
    for _ in range(8):
        expected += int(str(expected)[::-1])
    assert term.digits() == tuple(map(int, reversed(str(expected))))
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    metrics = term.metrics()
    behavior = term.behavior_metrics()

    assert metrics.higher_action_continuation_requests == 0
    assert metrics.higher_concrete_operation_evaluations == 0
    assert metrics.resource_work_counters["source_image_publications"] > 0
    assert metrics.resource_work_counters["reverse_recursive_completed_child_joins"] > 0
    assert metrics.resource_work_counters["reverse_provider_parent_substitutions"] > 0
    assert (
        metrics.resource_work_counters.get("source_image_primitive_applications", 0)
        == 0
    )
    assert metrics.resource_work_counters.get("sequential_generation_advances", 0) == 0
    assert (
        metrics.resource_work_counters.get(
            "reverse_recursive_direct_temporal_publications", 0
        )
        == 0
    )
    assert (
        metrics.resource_work_counters.get("reverse_recursive_terminal_publications", 0)
        == 0
    )
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert behavior.temporal_quotient_family == "reverse-add-source-cylinder"
