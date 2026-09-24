from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.carry.event_memory import event_memory_horizon
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import HashLifeBehaviorMetrics


def _exercise(
    term: PoweredCollatzTerm | ReverseAddPoweredTerm,
) -> tuple[HashLifeBehaviorMetrics, HashLifeBehaviorMetrics]:
    assert not hasattr(term, "_diamond_runtime")
    before = term.behavior_metrics()
    collatz = isinstance(term, PoweredCollatzTerm)
    if collatz:
        assert before.field_action_nodes == 0
        assert before.temporal_quotient_family == "collatz-dyadic-source-image"
    else:
        assert before.field_action_nodes > 0
    assert before.resource_audit_complete == 1
    assert before.resource_accounting_mismatch == 0
    assert before.unquotiented_recursive_application_description_nodes == 0
    assert before.representation_boundary_complete == 1
    if collatz:
        assert before.seed_payload_tile_nodes == 0
    else:
        assert before.seed_payload_tile_nodes > 0
    term.digit(0)
    after = term.behavior_metrics()
    runtime = term.metrics()
    assert after.resource_audit_complete == 1
    assert after.resource_accounting_mismatch == 0
    assert (
        after.forbidden_future_payloads == after.retained_unbounded_future_integers == 0
    )
    assert after.unquotiented_recursive_application_description_nodes == 0
    if collatz:
        assert isinstance(term, PoweredCollatzTerm)
        assert after.field_action_nodes == 0
        assert after.seed_application_temporal_action_nodes > 0
        assert term._power is None
        counters = runtime.resource_work_counters
        assert counters.get("collatz_physical_action_publications", 0) > 0
        assert counters.get("source_image_publications", 0) > 0
        assert counters.get("source_image_projection_publications", 0) > 0
        assert runtime.temporal_parent_requests == 0
        assert runtime.temporal_parent_compositions == 0
    else:
        assert after.field_action_nodes > 0
        assert runtime.bounded_application_enabled == 1
    assert runtime.sequential_generation_advances == 0
    assert runtime.higher_concrete_operation_evaluations == 0
    assert runtime.higher_action_continuation_requests == 0
    assert runtime.temporal_parent_requests == (
        runtime.temporal_parent_early_hits + runtime.temporal_parent_compositions
    )
    if not collatz:
        assert runtime.tile_scheduler_leaf_function_applications > 0
        assert runtime.completed_result_requests > 0
    assert before.bounded_temporal_runtime_cutover_complete == 1
    assert before.bounded_temporal_runtime_cutover_blocker == ""
    assert after.bounded_temporal_runtime_cutover_complete == 1
    assert after.bounded_temporal_runtime_cutover_blocker == ""
    return before, after


@pytest.mark.validation  # N=64 executed reverse release metrics and inventory.
def test_reverse_hashlife_reports_current_tile_action_work() -> None:
    term = ReverseAddPoweredTerm(196, 64)
    _, after = _exercise(term)
    assert after.temporal_quotient_family == "reverse-add-tile-hashlife"
    assert event_memory_horizon(10) == 20
    assert after.temporal_quotient_state_class_bound == after.local_interface_nodes > 0
    assert after.temporal_quotient_action_class_bound == after.field_action_nodes
    assert (
        after.bounded_application_nonlinear_branch_evaluations
        == after.primitive_transition_evaluations
        > 0
    )
    assert (
        after.bounded_application_exact_spatial_occurrences
        == after.canonical_tile_nodes
        > 0
    )
    assert after.source_leaf_visits > 0
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
    assert counters.get("collatz_physical_macro_bounded_base_steps", 0) > 0
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


@pytest.mark.validation  # Both families at N=64, including warm execution metrics.
def test_action_metrics_report_diamond_work_and_warm_response_reuse() -> None:
    for term in (ReverseAddPoweredTerm(196, 64), PoweredCollatzTerm(27, 64)):
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
        compositions = public.temporal_parent_compositions
        exponent = getattr(term, "generation", None)
        if exponent is None:
            assert isinstance(term, PoweredCollatzTerm)
            exponent = term.steps
        assert compositions <= 2 * exponent.bit_length() + 4
        assert public.temporal_parent_requests == (
            public.temporal_parent_early_hits + public.temporal_parent_compositions
        )
        assert (
            public.bounded_application_nonlinear_branch_evaluations
            == public.primitive_transition_evaluations
            > 0
        )
        assert public.bounded_application_primitive_step_evaluations == 0
        assert public.bounded_application_exact_endpoint_entries == 0
        requests = public.resource_work_counters["point_response_requests"]
        hits = public.resource_work_counters.get("point_response_cache_hits", 0)
        term.digit(0)
        repeated_public = term.metrics()
        assert repeated_public.temporal_parent_compositions == compositions
        assert (
            repeated_public.resource_work_counters["point_response_requests"]
            == requests + 1
        )
        assert (
            repeated_public.resource_work_counters["point_response_cache_hits"]
            == hits + 1
        )
