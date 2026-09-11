"""Schema-six metrics separate proof metadata and production resources."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from typing import TYPE_CHECKING

from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import LedgerMetrics
    from number_compiler.sequences.collatz.block_power import (
        CollatzPhysicalBlockMetrics,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPowerMetrics


def assert_node_partition(
    metrics: LedgerMetrics | CollatzPhysicalBlockMetrics | ReverseAddPowerMetrics,
) -> None:
    assert metrics.metrics_schema_version == 6
    assert metrics.resource_observed_nodes == (
        metrics.source_payload_nodes
        + metrics.temporal_program_nodes
        + metrics.canonical_transfer_nodes
        + metrics.spatial_binding_nodes
        + metrics.finite_port_state_nodes
        + metrics.exact_endpoint_nodes
        + metrics.other_retained_nodes
        + metrics.spatial_action_program_nodes
        + metrics.image_action_nodes
        + metrics.diamond_cell_nodes
        + metrics.field_action_nodes
        + metrics.algebraic_component_nodes
        + metrics.field_geometry_nodes
        + metrics.production_residual_state_nodes
        + metrics.primitive_behavioral_quotient_nodes
        + metrics.semantic_function_nodes
        + metrics.diamond_quotient_nodes
        + metrics.semantic_signature_nodes
        + metrics.exact_microblock_nodes
        + metrics.canonical_tile_nodes
        + metrics.tile_alphabet_nodes
        + metrics.future_behavior_profile_nodes
        + metrics.future_behavior_class_nodes
    )
    assert metrics.transfer_summary_nodes == metrics.canonical_transfer_nodes
    assert (
        metrics.temporal_program_nodes
        == metrics.compiler_program_nodes + metrics.application_program_nodes
    )
    assert (
        metrics.cache_slots
        == metrics.resource_observed_entries
        == metrics.resource_ledger_entries
    )


def test_reverse_diamond_does_not_report_proof_states_as_runtime_classes() -> None:
    term = ReverseAddPoweredTerm(196, 32)
    term.digit(0)
    metrics, behavior = term.metrics(), term.behavior_metrics()
    assert_node_partition(metrics)
    assert (
        metrics.bounded_application_temporal_state_classes
        == metrics.local_interface_nodes
        > 0
    )
    assert (
        metrics.bounded_application_temporal_action_classes
        == metrics.field_action_nodes
    )
    assert (
        metrics.reverse_t2_proof_left_state_classes,
        metrics.reverse_t2_proof_right_state_classes,
    ) == (757, 179)
    assert metrics.temporal_parent_requests > 0
    assert metrics.temporal_parent_requests == (
        metrics.temporal_parent_early_hits + metrics.temporal_parent_compositions
    )
    assert metrics.bounded_application_nonlinear_branch_evaluations == (
        metrics.primitive_transition_evaluations
    )
    assert metrics.bounded_application_exact_endpoint_entries == 0
    assert metrics.forbidden_future_payloads == 0
    assert metrics.whole_word_sweeps == metrics.proof_machine_applications == 0
    assert behavior.temporal_quotient_family == "reverse-add-tile-hashlife"
    assert behavior.bounded_temporal_runtime_cutover_complete == 1
    assert behavior.bounded_temporal_runtime_cutover_blocker == ""


def test_query_memo_eviction_does_not_change_proof_metadata_or_runtime_classes() -> (
    None
):
    term = ReverseAddPoweredTerm(196, 24)
    expected = term.digit(0)
    before = term.metrics()
    term._ledger.evict_query_memos()
    evicted = term.metrics()
    assert_node_partition(evicted)
    assert evicted.temporal_program_nodes == before.temporal_program_nodes
    assert (
        evicted.bounded_application_temporal_state_classes
        == evicted.local_interface_nodes
        > 0
    )
    assert evicted.reverse_t2_proof_left_state_classes == 757
    assert evicted.reverse_t2_proof_right_state_classes == 179
    assert (
        evicted.bounded_application_retained_entries
        < before.bounded_application_retained_entries
    )
    assert evicted.cache_slots < before.cache_slots
    assert term.digit(0) == expected
    assert_node_partition(term.metrics())


def test_collatz_query_eviction_preserves_canonical_temporal_compositions() -> None:
    """Eviction may rebuild occurrence bindings, never the powered action DAG."""
    term = PoweredCollatzTerm(27, 16)
    expected = term.digit(0)
    before = dict(term._ledger.counters)
    assert before.get("tile_temporal_action_publications", 0) > 0

    term._ledger.evict_query_memos()
    assert term.digit(0) == expected
    after = term._ledger.counters

    assert after.get("tile_temporal_action_publications", 0) == before.get(
        "tile_temporal_action_publications", 0
    )
    assert after.get("temporal_parent_compositions", 0) == before.get(
        "temporal_parent_compositions", 0
    )


def test_collatz_diamond_does_not_report_proof_states_as_runtime_classes() -> None:
    term = PoweredCollatzTerm(27, 32)
    term.digit(0)
    metrics = term.metrics()
    assert_node_partition(metrics)
    assert (
        metrics.bounded_application_temporal_state_classes
        == metrics.local_interface_nodes
        > 0
    )
    assert (
        metrics.bounded_application_temporal_action_classes
        == metrics.field_action_nodes
    )
    assert (
        metrics.collatz_c4_proof_left_state_classes,
        metrics.collatz_c4_proof_right_state_classes,
    ) == (50, 90)
    assert metrics.temporal_parent_requests > 0
    assert metrics.bounded_application_nonlinear_branch_evaluations == (
        metrics.primitive_transition_evaluations
    )
    assert metrics.bounded_application_exact_endpoint_entries == 0
    assert metrics.forbidden_future_payloads == 0
    assert metrics.whole_word_sweeps == metrics.proof_machine_applications == 0


def test_exact_spatial_population_does_not_add_work_visits_to_retained_nodes() -> None:
    term = PoweredCollatzTerm(27, 16)
    term.digit(0)
    before = term.metrics()
    term._ledger.bump("source_leaf_reads", 101)
    after = term.metrics()
    assert after.source_leaf_visits == before.source_leaf_visits + 101
    # Canonical source and future tiles are the exact spatial population on the
    # production route.  Source-cell and endpoint arenas belong to retired or
    # explicit-lowering carriers and are not a substitute for this inventory.
    assert (
        after.bounded_application_exact_spatial_occurrences
        == after.canonical_tile_nodes
    )
    assert after.bounded_application_exact_spatial_occurrences == (
        before.bounded_application_exact_spatial_occurrences
    )


def test_geometry_population_has_its_own_inventory_unit() -> None:
    from number_compiler.hashlife.actions.field_actions import (
        FieldGeometry,
        FieldGeometryArena,
    )

    ledger = ResourceLedger()
    geometries = FieldGeometryArena(ledger)
    geometries.intern(FieldGeometry(1))
    geometries.intern(FieldGeometry(2))
    geometries.intern(FieldGeometry(1))
    report = collect_ledger_metrics(ledger)
    assert report.field_geometry_nodes == 2
    assert report.other_retained_nodes == 0
    assert report.resource_observed_nodes == 2
    assert report.resource_observed_entries == 4
    assert_node_partition(report)


def test_generic_diamond_bindings_are_counted_by_their_actual_runtime_roles() -> None:
    ledger = ResourceLedger()
    application = HashLifeBlockIndex(
        DigitNormalizeBlockEffect(10),
        (2,) * 16,
        logical_length=16,
        ledger=ledger,
    )
    assert application.direct_powered_point(12) == 2
    metrics = collect_ledger_metrics(ledger)
    assert_node_partition(metrics)
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    runtime = application._lazy_application
    assert type(runtime) is LazyProjection
    results = runtime.scheduler.results
    assert metrics.powered_interface_entries == results.retained_interfaces > 0
    assert metrics.completed_result_entries == results.retained_results > 0
    assert metrics.local_interface_nodes > 0
    assert metrics.canonical_tile_nodes == len(runtime.scheduler.tiles._nodes) > 0


def test_node_categories_follow_observed_records_not_unpublished_reservations() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("programs", "action_program")
    ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    metrics = collect_ledger_metrics(ledger)
    assert metrics.resource_ledger_nodes == 1
    assert metrics.resource_observed_nodes == metrics.temporal_program_nodes == 0
    assert metrics.resource_accounting_mismatch > 0


def test_additional_registered_nodes_are_visible_in_the_other_category() -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken

    ledger = ResourceLedger()
    owner = ledger.register("metadata", "diagnostic_metadata")
    records: LedgerList[object]
    records = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(ArenaToken("metadata"))
    metrics = collect_ledger_metrics(ledger)
    assert_node_partition(metrics)
    assert metrics.other_retained_nodes == 1
    assert metrics.spatial_binding_nodes == metrics.canonical_transfer_nodes == 0


def test_literal_and_reflection_work_distinguishes_cache_and_identity_shortcuts() -> (
    None
):
    from devtools.proofs.carry_interval_effects import CarryActionQuotientArena
    from number_compiler.arithmetic.functions.finite_port_action import PortVariable

    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    action = arena.interval_word((0, 10), base=10, port=port)
    reflected = arena.reflect_interval(action)
    assert reflected != action
    assert arena.reflect_interval(action) == reflected
    identity = arena.interval_identity(port)
    assert arena.reflect_interval(identity) == identity
    report = collect_ledger_metrics(arena.ledger)
    assert_node_partition(report)
    assert (
        report.interval_literal_requests
        == report.interval_literal_cache_hits + report.interval_literal_evaluations
    )
    assert report.interval_literal_cache_hits > 0
    assert report.interval_literal_evaluations == 3
    assert report.interval_reflection_requests == (
        report.interval_reflection_cache_hits
        + report.interval_reflection_identity_hits
        + report.interval_reflection_evaluations
    )
    assert report.interval_reflection_cache_hits == 1
    assert report.interval_reflection_identity_hits == 1
    assert report.interval_reflection_evaluations == 1
    assert report.resource_accounting_mismatch == report.forbidden_future_payloads == 0


def test_work_and_temporary_component_peaks_are_forwarded_without_inventing_totals() -> (
    None
):
    ledger = ResourceLedger()
    ledger.bump("finite_port_applications", 11)
    ledger.bump("finite_port_decision_visits", 19)
    ledger.bump("reverse_carry_function_classifications", 5)
    ledger.bump("reverse_carry_workspace_peak", 4)
    ledger.bump("reverse_evaluator_stack_peak", 9)
    ledger.bump("collatz_evaluator_stack_peak_frames", 7)
    metrics = collect_ledger_metrics(ledger)
    assert metrics.finite_port_applications == 11
    assert metrics.finite_port_decision_visits == 19
    assert metrics.reverse_carry_function_classifications == 5
    assert metrics.resource_workspace_peaks == {
        "reverse_carry_workspace_peak": 4,
        "reverse_evaluator_stack_peak": 9,
        "collatz_evaluator_stack_peak_frames": 7,
    }
    assert metrics.resource_observed_nodes == metrics.cache_slots == 0
    assert metrics.representation_boundary_complete == 1
    # Peaks are component maxima, which need not occur simultaneously.
    assert "total_workspace" not in metrics.resource_workspace_peaks


def test_point_response_domain_accepts_decimal_nine_and_rejects_a_wide_payload() -> (
    None
):
    from number_compiler.projection.point_response import PointResponse

    term = ReverseAddPoweredTerm(18, 1)
    assert term.digit(0) == 9
    ledger = term._ledger
    clean = collect_ledger_metrics(ledger)
    assert clean.representation_boundary_complete == 1
    assert clean.retained_point_response_scalars == 1
    assert clean.exact_endpoint_nodes == 0
    response = next(
        value
        for _, container in ledger.iter_containers()
        for value in (
            list(container.values())
            if isinstance(container, Mapping)
            else list(container)
            if isinstance(container, Iterable)
            else []
        )
        if isinstance(value, PointResponse)
    )
    owner = ledger.register("forged-response", "observation_memo")
    records: LedgerList[object]
    records = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(PointResponse(response.program, response.position, 1 << 1000))
    rejected = collect_ledger_metrics(ledger)
    assert rejected.forbidden_future_payloads > 0
    assert rejected.representation_boundary_complete == 0


def test_response_record_collection_cannot_become_a_tape_under_semantic_wrappers() -> (
    None
):
    from number_compiler.projection.point_response import PointResponse

    term = ReverseAddPoweredTerm(18, 1)
    term.digit(0)
    register = term._point_index()._point_response
    saved = register._value[0]
    term._ledger.reserve(register.owner, entries=3, nodes=3)
    register._value.extend(
        PointResponse(saved.program, position, position) for position in (1, 2, 3)
    )
    metrics = collect_ledger_metrics(term._ledger)
    assert metrics.retained_point_response_scalars == 4
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads > 0
    assert metrics.representation_boundary_complete == 0


def test_legitimate_response_cannot_be_reused_as_a_canonical_action_payload() -> None:
    term = ReverseAddPoweredTerm(18, 1)
    term.digit(0)
    response = term._point_index()._point_response._value[0]
    owner = term._ledger.register("counterfeit-action", "canonical_transfer")
    records: LedgerList[object]
    records = term._ledger.make_list(owner)
    term._ledger.reserve(owner, entries=1, nodes=1)
    records.append(response)
    metrics = collect_ledger_metrics(term._ledger)
    assert metrics.forbidden_future_payloads > 0
    assert metrics.representation_boundary_complete == 0


def test_boundary_validation_work_is_separate_from_proof_publication_slots() -> None:
    ledger = ResourceLedger()
    quantities = {
        "collatz_radix_boundary_validation_requests": 7,
        "collatz_radix_boundary_validation_visits": 11,
        "collatz_radix_boundary_proof_hits": 13,
        "collatz_radix_boundary_proof_publications": 11,
    }
    for counter, quantity in quantities.items():
        ledger.bump(counter, quantity)
    report = collect_ledger_metrics(ledger)
    for counter, quantity in quantities.items():
        assert getattr(report, counter) == quantity
    assert report.total_internal_action_work == 24
    assert report.resource_observed_entries == 0


def test_tile_radix_publications_and_observations_count_as_work() -> None:
    ledger = ResourceLedger()
    quantities = {
        "tile_radix_stage_publications": 5,
        "tile_radix_digit_observations": 276,
    }
    for counter, quantity in quantities.items():
        ledger.bump(counter, quantity)
    report = collect_ledger_metrics(ledger)
    for counter, quantity in quantities.items():
        assert getattr(report, counter) == quantity
    assert report.total_internal_action_work == 281
    assert report.resource_observed_entries == 0


def test_higher_interpreter_counts_frames_instead_of_one_call_as_one_unit() -> None:
    ledger = ResourceLedger()
    ledger.bump("higher_semantic_evaluations", 2)
    ledger.bump("higher_semantic_task_frames", 301)
    ledger.bump("temporal_leaf_diamond_descents", 17)
    report = collect_ledger_metrics(ledger)
    assert report.higher_semantic_evaluations == 2
    assert report.higher_semantic_task_frames == 301
    assert report.temporal_leaf_diamond_descents == 17
    assert report.total_internal_action_work == 318


def test_composed_tile_work_is_visible_without_continuation_execution() -> None:
    term = ReverseAddPoweredTerm(196, 16)
    term.digit(term.maximum_width // 3)
    report = term.metrics()
    assert report.powered_absorption_requests > 0
    causal_frames = report.resource_work_counters["tile_causal_frames"]
    assert causal_frames > 0
    assert report.higher_action_continuation_requests == 0
    assert causal_frames == term._ledger.counters["tile_causal_frames"]


def test_absorbed_span_is_metadata_not_additive_execution_work() -> None:
    ledger = ResourceLedger()
    quantities = {
        "powered_absorption_requests": 5,
        "powered_absorption_early_hits": 2,
        "powered_absorption_evaluations": 3,
        "powered_absorption_successes": 4,
        "powered_absorption_max_span": 1024,
        "proof_artifact_builds": 1,
        "proof_artifact_hits": 2,
        "proof_artifact_loading_work": 19,
    }
    for counter, quantity in quantities.items():
        ledger.bump(counter, quantity)
    before = ledger.snapshot()
    report = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    for counter, quantity in quantities.items():
        assert getattr(report, counter) == quantity
    assert report.total_internal_action_work == 24
    assert report.resource_observed_entries == 0
