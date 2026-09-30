from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.carry.event_memory import event_memory_horizon
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.source_image_assertions import assert_physical_publications

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import HashLifeBehaviorMetrics


def _exercise(
    term: PoweredCollatzTerm | ReverseAddPoweredTerm,
) -> tuple[HashLifeBehaviorMetrics, HashLifeBehaviorMetrics]:
    assert not hasattr(term, "_diamond_runtime")
    before = term.behavior_metrics()
    before_audit = collect_ledger_metrics(term._ledger)
    collatz = isinstance(term, PoweredCollatzTerm)
    if collatz:
        assert before.field_action_nodes == 0
        assert before.temporal_quotient_family == "collatz-dyadic-source-image"
    else:
        assert before.field_action_nodes == 0
    assert before_audit.resource_audit_complete == 1
    assert before.resource_accounting_mismatch == 0
    assert before.unquotiented_recursive_application_description_nodes == 0
    assert before_audit.representation_boundary_complete == 1
    if collatz:
        assert before.seed_payload_tile_nodes == 0
    else:
        assert before.temporal_quotient_family == "reverse-add-source-cylinder"
        assert before.seed_payload_tile_nodes == 0
    term.digit(0)
    after = term.behavior_metrics()
    runtime = term.metrics()
    after_audit = collect_ledger_metrics(term._ledger)
    assert after_audit.resource_audit_complete == 1
    assert after.resource_accounting_mismatch == 0
    assert (
        after_audit.forbidden_future_payloads
        == after_audit.retained_unbounded_future_integers
        == 0
    )
    assert after.unquotiented_recursive_application_description_nodes == 0
    if collatz:
        assert isinstance(term, PoweredCollatzTerm)
        assert after.field_action_nodes == 0
        assert after.seed_application_temporal_action_nodes > 0
        assert term._power is None
        counters = runtime.resource_work_counters
        assert_physical_publications(counters)
        assert runtime.temporal_parent_requests == 0
        assert runtime.temporal_parent_compositions == 0
    else:
        assert after.field_action_nodes == 0
        assert after.temporal_quotient_family == "reverse-add-source-cylinder"
        assert after.seed_application_temporal_action_nodes > 0
        counters = runtime.resource_work_counters
        assert counters.get("source_image_publications", 0) > 0
        assert counters.get("source_image_projection_publications", 0) > 0
    assert runtime.sequential_generation_advances == 0
    assert runtime.higher_concrete_operation_evaluations == 0
    assert runtime.higher_action_continuation_requests == 0
    assert runtime.temporal_parent_requests == (
        runtime.temporal_parent_early_hits + runtime.temporal_parent_compositions
    )
    return before, after


@pytest.mark.validation  # N=64 exact reverse output and source-image accounting.
def test_reverse_source_image_reports_exact_output_and_publications() -> None:
    expected = 196
    for _ in range(64):
        expected += int(str(expected)[::-1])
    term = ReverseAddPoweredTerm(196, 64)
    assert term.digits() == tuple(map(int, reversed(str(expected))))
    _, after = _exercise(term)
    assert after.temporal_quotient_family == "reverse-add-source-cylinder"
    assert event_memory_horizon(10) == 20
    assert after.temporal_quotient_state_class_bound == 0
    assert after.temporal_quotient_action_class_bound == 0
    assert after.field_action_nodes == 0
    assert after.higher_concrete_operation_evaluations == 0


@pytest.mark.validation  # N=64 executed Collatz release metrics and inventory.
def test_collatz_hashlife_reports_current_tile_action_work() -> None:
    _, after = _exercise(PoweredCollatzTerm(27, 64))
    assert after.temporal_quotient_family == "collatz-dyadic-source-image"
    assert after.temporal_quotient_state_class_bound == 0
    assert after.temporal_quotient_action_class_bound == 0
    assert after.seed_application_temporal_action_nodes > 0
    assert after.seed_application_temporal_description_nodes > 0
    counters = after.resource_work_counters
    assert counters.get("collatz_physical_temporal_run_actions", 0) > 0
    assert counters.get("source_image_primitive_applications", 0) > 0
    assert counters.get("source_image_publications", 0) > 0


def test_seed_payload_description_is_independent_of_temporal_generation() -> None:
    reverse_small = ReverseAddPoweredTerm(196, 8).behavior_metrics()
    reverse_large = ReverseAddPoweredTerm(196, 16).behavior_metrics()
    assert (
        reverse_small.seed_payload_tile_nodes == reverse_large.seed_payload_tile_nodes
    )
    collatz_small = PoweredCollatzTerm(27, 8).behavior_metrics()
    collatz_large = PoweredCollatzTerm(27, 16).behavior_metrics()
    assert (
        collatz_small.seed_payload_tile_nodes == collatz_large.seed_payload_tile_nodes
    )


@pytest.mark.validation  # Both families at N=64, including warm image reuse.
def test_action_metrics_report_image_publication_and_warm_response_reuse() -> None:
    reverse_expected = 196
    for _ in range(64):
        reverse_expected += int(str(reverse_expected)[::-1])
    for term in (ReverseAddPoweredTerm(196, 64), PoweredCollatzTerm(27, 64)):
        if isinstance(term, ReverseAddPoweredTerm):
            assert term.digits() == tuple(map(int, reversed(str(reverse_expected))))
        else:
            expected = 27
            for _ in range(term.steps):
                expected = 3 * expected + 1 if expected & 1 else expected // 2
            assert term.materialize(max_bits=10_000) == expected
        term.digit(0)
        public = term.metrics()
        if isinstance(term, PoweredCollatzTerm):
            counters = public.resource_work_counters
            publications = counters.get("source_image_publications", 0)
            assert publications > 0
            assert public.temporal_parent_requests == 0
            assert public.temporal_parent_compositions == 0
            assert term._power is None
            hits = counters.get("microblock_hits", 0)
            term.digit(0)
            repeated = term.metrics()
            assert (
                repeated.resource_work_counters.get("source_image_publications", 0)
                == publications
            )
            assert repeated.resource_work_counters.get("microblock_hits", 0) > hits
            continue
        counters = public.resource_work_counters
        publications = counters["source_image_publications"]
        projection_publications = counters["source_image_projection_publications"]
        assert publications > 0 and projection_publications > 0
        term.digit(0)
        repeated_public = term.metrics()
        assert (
            repeated_public.resource_work_counters["source_image_publications"]
            == publications
        )
        assert (
            repeated_public.resource_work_counters[
                "source_image_projection_publications"
            ]
            == projection_publications
        )
