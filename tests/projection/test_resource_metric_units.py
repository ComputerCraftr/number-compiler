"""Schema-eight metrics report retained oracles and production resources."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.assertions import collect_counter_quantities

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import LedgerMetrics
    from number_compiler.sequences.collatz.block_power import (
        CollatzPhysicalBlockMetrics,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPowerMetrics


def assert_node_partition(
    metrics: LedgerMetrics | CollatzPhysicalBlockMetrics | ReverseAddPowerMetrics,
) -> None:
    assert metrics.metrics_schema_version == 8
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


def test_collatz_query_eviction_preserves_canonical_temporal_compositions() -> None:
    """Eviction reuses the authenticated source image and powered action DAG."""
    term = PoweredCollatzTerm(27, 16)
    expected = term.digit(0)
    before = dict(term.resource_ledger.counters)
    assert before.get("source_image_publications", 0) > 0

    term.resource_ledger.evict_query_memos()
    assert term.digit(0) == expected
    after = term.resource_ledger.counters

    assert after.get("source_image_publications", 0) == before.get(
        "source_image_publications", 0
    )
    assert after.get("source_image_primitive_applications", 0) == before.get(
        "source_image_primitive_applications", 0
    )
    assert after["source_image_publications"] == before["source_image_publications"]
    assert (
        after["direct_powered_point_queries"]
        == before["direct_powered_point_queries"] + 1
    )


def test_collatz_source_image_metrics_do_not_report_proof_sizes_as_runtime_classes() -> (
    None
):
    term = PoweredCollatzTerm(27, 32)
    term.digit(0)
    metrics = term.metrics()
    assert_node_partition(metrics)
    assert metrics.local_interface_nodes == metrics.field_action_nodes == 0
    assert metrics.canonical_tile_nodes == 0
    assert metrics.bounded_application_exact_endpoint_entries == 0
    assert collect_ledger_metrics(term.resource_ledger).forbidden_future_payloads == 0
    assert metrics.whole_word_sweeps == metrics.proof_machine_applications == 0
    assert metrics.resource_work_counters["source_image_publications"] > 0
    assert metrics.resource_work_counters["source_image_projection_publications"] > 0


def test_exact_spatial_population_does_not_add_work_visits_to_retained_nodes() -> None:
    term = PoweredCollatzTerm(27, 16)
    term.digit(0)
    before = term.metrics()
    before_inventory = term.resource_ledger.snapshot().inventory
    term.resource_ledger.bump("source_leaf_reads", 101)
    after = term.metrics()
    after_inventory = term.resource_ledger.snapshot().inventory
    assert after.source_leaf_visits == before.source_leaf_visits + 101
    before_images = sum(
        row.observed_nodes or 0
        for row in before_inventory
        if row.role == "source_image"
    )
    after_images = sum(
        row.observed_nodes or 0 for row in after_inventory if row.role == "source_image"
    )
    assert after_images == before_images > 0
    assert after.canonical_tile_nodes == before.canonical_tile_nodes == 0


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


def test_public_projection_metrics_do_not_run_deep_audits() -> None:
    from unittest.mock import patch

    ledger = ResourceLedger()
    application = HashLifeBlockIndex(
        DigitNormalizeBlockEffect(10),
        (2,) * 16,
        logical_length=16,
        ledger=ledger,
    )
    application.direct_powered_point(12)
    before = dict(ledger.counters)

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("projection metrics invoked a deep audit")

    with (
        patch(
            "number_compiler.resources.metric_collection.audit_registered_payloads",
            forbidden,
        ),
        patch(
            "number_compiler.resources.metric_collection.audit_execution_ownership",
            forbidden,
        ),
    ):
        report = application.metrics()

    assert report.resource_accounting_mismatch == 0
    assert dict(ledger.counters) == before


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
    from devtools.verification.carry_interval_effects import CarryActionQuotientArena
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


def test_boundary_validation_work_is_separate_from_proof_publication_slots() -> None:
    ledger = ResourceLedger()
    quantities = {
        "collatz_radix_boundary_validation_requests": 7,
        "collatz_radix_boundary_validation_visits": 11,
        "collatz_radix_boundary_proof_hits": 13,
        "collatz_radix_boundary_proof_publications": 11,
    }
    report = collect_counter_quantities(ledger, quantities)
    assert report.total_internal_action_work == 24
    assert report.resource_observed_entries == 0


def test_tile_radix_publications_and_observations_count_as_work() -> None:
    ledger = ResourceLedger()
    quantities = {
        "tile_radix_stage_publications": 5,
        "tile_radix_digit_observations": 276,
    }
    report = collect_counter_quantities(ledger, quantities)
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
