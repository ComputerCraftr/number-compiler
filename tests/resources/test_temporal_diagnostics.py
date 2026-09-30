"""Schema-eight temporal reporting distinguishes absent and measured zero work."""

from __future__ import annotations

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.temporal_diagnostics import (
    TemporalExecutionDiagnostics,
    collect_temporal_diagnostics,
    collect_temporal_diagnostics_snapshot,
)


def _collect(counters: dict[str, int]) -> TemporalExecutionDiagnostics:
    return collect_temporal_diagnostics(
        counters,
        entries=3,
        nodes=4,
        peak_entries=5,
        peak_nodes=6,
        audit_complete=True,
        accounting_mismatch=0,
    )


def test_explicit_mahler_audit_does_not_reconstruct_endpoint() -> None:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cli_requests import parse_request
    from number_compiler.api.number_api import AntihydraTermPayload, NumberCompiler

    request = parse_request(["antihydra", "--nth", "65", "--info", "mahler"])
    assert request is not None
    query = QueryContext(request, NumberCompiler())
    query.information()
    payload = query.term.payload
    assert isinstance(payload, AntihydraTermPayload)
    ledger = payload.term.ledger
    before = dict(ledger.counters)
    version = ledger.mutation_version
    metrics = collect_ledger_metrics(ledger)
    assert metrics.resource_audit_complete
    assert metrics.resource_accounting_mismatch == 0
    assert ledger.mutation_version == version
    assert ledger.counters["mahler_source_validation_operand_bits"] > before.get(
        "mahler_source_validation_operand_bits", 0
    )
    for name in (
        "antihydra_arithmetic_fiber_endpoint_demands",
        "antihydra_arithmetic_aggregate_demands",
    ):
        assert ledger.counters.get(name, 0) == before.get(name, 0)


def test_uninstrumented_lanes_are_unavailable_not_zero() -> None:
    record = _collect({})
    assert record.schema_version == 8
    assert record.action.publications is None
    assert record.application.exact_hits is None
    assert record.application.publications is None
    assert record.projection.publications is None
    assert record.construction.postorder_frames is None
    assert record.construction.source_image_adapter_registrations is None
    assert record.construction.arithmetic_result_publications is None
    assert record.construction.bootstrap_admission_steps is None
    assert record.demand.point_requests is None
    assert record.demand.length_requests is None
    assert record.stream.requests is None
    assert record.observations.physical_roof_evaluations is None
    assert record.observations.arithmetic_result_validation_blocks is None
    assert record.observations.arithmetic_result_validation_reconstructions is None
    assert record.observations.arithmetic_result_validation_operand_bits is None
    assert record.observations.mahler_source_composed_image_reads is None
    assert record.observations.mahler_associated_action_demands is None
    assert (record.resources.entries, record.resources.nodes) == (3, 4)


@pytest.mark.parametrize("prefix", ("collatz_physical", "antihydra_arithmetic"))
def test_run_measurements_share_schema_without_evaluation(prefix: str) -> None:
    ledger = ResourceLedger()
    ledger.bump(f"{prefix}_action_publications")
    ledger.bump(f"{prefix}_temporal_run_actions", 3)
    ledger.bump(f"{prefix}_temporal_zero_run_pumps", 2)
    ledger.bump(f"{prefix}_temporal_one_run_pumps", 1)
    ledger.bump(f"{prefix}_temporal_punctured_event_actions", 2)
    ledger.bump(f"{prefix}_temporal_punctured_event_symbols", 7)
    ledger.bump(f"{prefix}_run_contraction_publications")
    before = dict(ledger.counters)
    record = collect_temporal_diagnostics_snapshot(ledger).family_work[0]
    assert (record.punctured_event_actions, record.punctured_event_symbols) == (2, 7)
    assert (record.run_actions, record.zero_run_pumps, record.one_run_pumps) == (
        3,
        2,
        1,
    )
    assert record.run_contraction_publications == 1
    assert record.represented_cycle_repetitions is None
    assert ledger.counters == before


def test_comma_macro_reuse_is_distinct_from_represented_steps() -> None:
    ledger = ResourceLedger()
    ledger.bump("comma_boundary_prefix_applications", 2)
    ledger.bump("comma_boundary_represented_transitions", 10**12)
    ledger.bump("comma_boundary_template_hits", 1)
    ledger.bump("comma_relative_guard_checks", 4)
    ledger.bump("comma_relative_cycle_rebindings", 1)
    ledger.bump("comma_boundary_seal_checks", 9)
    ledger.bump("comma_boundary_seal_retained_slots", 30)
    ledger.bump("comma_boundary_seal_retained_integer_bits", 1500)
    before = dict(ledger.counters)
    version = ledger.mutation_version
    report = collect_temporal_diagnostics_snapshot(ledger)
    assert report.comma.boundary_prefix_applications == 2
    assert report.comma.boundary_represented_transitions == 10**12
    assert report.comma.boundary_template_hits == 1
    assert report.comma.relative_guard_checks == 4
    assert report.comma.relative_cycle_rebindings == 1
    assert report.comma.boundary_seal_checks == 9
    assert report.comma.boundary_seal_retained_slots == 30
    assert report.comma.boundary_seal_retained_integer_bits == 1500
    assert report.comma.boundary_template_retained_nodes is None
    assert report.comma.operations is None
    assert ledger.counters == before
    assert ledger.mutation_version == version


@pytest.mark.parametrize("prefix", ("collatz_physical", "antihydra_arithmetic"))
def test_balanced_work_is_distinct_from_scheduler_and_interner_hits(
    prefix: str,
) -> None:
    counters = {
        f"{prefix}_action_publications": 1,
        f"{prefix}_action_hits": 9,
        f"{prefix}_transient_leaf_steps": 512,
        f"{prefix}_balanced_effect_compositions": 7,
        f"{prefix}_balanced_effect_composition_operand_bits": 18000,
        f"{prefix}_composite_cutover_chunks": 0,
        f"{prefix}_composite_cutover_publications": 1,
        f"{prefix}_saturated_support_publications": 1,
        f"{prefix}_balanced_effect_memo_lookups": 10,
        f"{prefix}_balanced_effect_memo_hits": 3,
        f"{prefix}_balanced_effect_memo_misses": 7,
        f"{prefix}_balanced_effect_memo_publications": 7,
        f"{prefix}_finite_block_lookups": 23,
        f"{prefix}_finite_block_hits": 12,
        f"{prefix}_finite_block_misses": 11,
        f"{prefix}_finite_block_publications": 10,
        f"{prefix}_finite_block_evictions": 2,
        f"{prefix}_finite_block_cold_atoms": 4,
        f"{prefix}_finite_block_cold_steps": 16,
    }
    family = _collect(counters).family_work[0]
    assert family.transient_leaf_steps == 512
    assert family.balanced_effect_compositions == 7
    assert family.balanced_macro_compositions is None
    assert family.composite_cutover_chunks == 0
    assert family.composite_cutover_publications == 1
    assert family.saturated_support_publications == 1
    assert family.action_hits == 9
    assert family.balanced_effect_memo_lookups == 10
    assert family.balanced_effect_memo_hits == 3
    assert family.balanced_effect_memo_misses == 7
    assert family.balanced_effect_memo_publications == 7
    assert family.balanced_effect_memo_evictions is None
    assert family.finite_block_lookups == 23
    assert family.finite_block_hits == 12
    assert family.finite_block_misses == 11
    assert family.finite_block_publications == 10
    assert family.finite_block_evictions == 2
    assert family.finite_block_cold_atoms == 4
    assert family.finite_block_cold_steps == 16
    assert family.operand_bits == (
        (f"{prefix}_balanced_effect_composition_operand_bits", 18000),
    )
    assert counters[f"{prefix}_action_hits"] == 9


def test_source_image_lanes_preserve_distinct_reuse_and_work_units() -> None:
    record = _collect(
        {
            "source_image_adapter_registrations": 1,
            "source_image_publications": 9,
            "source_image_origin_publications": 2,
            "source_image_application_publications": 7,
            "source_image_application_requests": 1,
            "source_image_application_attempts": 12,
            "source_image_application_hits": 3,
            "source_image_relative_transfer_hits": 4,
            "source_image_application_misses": 5,
            "source_image_projection_requests": 11,
            "source_image_projection_hits": 5,
            "source_image_projection_misses": 6,
            "source_image_projection_publications": 6,
            "source_image_postorder_frames": 12,
            "source_image_primitive_applications": 0,
            "source_image_chronological_compositions": 1,
            "source_image_demanded_composite_applications": 2,
            "collatz_physical_action_publications": 7,
            "collatz_physical_action_requests": 9,
            "collatz_physical_action_hits": 2,
            "collatz_physical_action_misses": 7,
            "collatz_physical_macro_requests": 8,
            "collatz_physical_macro_bounded_base_steps": 11,
            "collatz_physical_macro_compositions": 13,
            "collatz_physical_macro_bounded_base_operand_bits": 99,
        }
    )
    assert record.action.publications == 7
    assert record.action.requests == 9
    assert record.action.exact_hits == 2
    assert record.action.misses == 7
    assert record.application.exact_hits == 3
    assert record.application.transported_hits == 4
    assert record.application.publications == 7
    assert record.application.requests == 1
    assert record.application.attempts == 12
    assert record.application.misses == 5
    assert record.projection.requests == 11
    assert record.projection.exact_hits == 5
    assert record.projection.misses == 6
    assert record.projection.publications == 6
    assert record.construction.primitive_applications == 0
    assert record.construction.composite_applications is None
    assert record.construction.demanded_composite_applications == 2
    assert record.family_work[0].bounded_base_steps == 11
    assert record.family_work[0].operand_bits == (
        ("collatz_physical_macro_bounded_base_operand_bits", 99),
    )
    # The applied composite bypasses scheduler primitive descent, but base
    # source discovery remains visible in a separate lane.
    assert record.family_work[0].bounded_base_steps > 0


def test_explicit_zero_is_distinct_from_missing_instrument() -> None:
    record = _collect(
        {
            "source_image_publications": 1,
            "source_image_origin_publications": 1,
            "source_image_application_publications": 0,
            "source_image_composite_applications": 0,
            "recursive_output_stream_requests": 0,
        }
    )
    assert record.application.publications == 0
    assert record.construction.composite_applications == 0
    assert record.construction.primitive_applications is None
    assert record.stream.requests == 0
    assert record.stream.emitted is None


def test_arithmetic_result_validation_work_has_separate_observation_units() -> None:
    record = _collect(
        {
            "arithmetic_result_validation_blocks": 2,
            "arithmetic_result_validation_reconstructions": 3,
            "arithmetic_result_validation_operand_bits": 145,
        }
    )
    assert record.observations.arithmetic_result_validation_blocks == 2
    assert record.observations.arithmetic_result_validation_reconstructions == 3
    assert record.observations.arithmetic_result_validation_operand_bits == 145
    assert record.observations.arithmetic_returns is None


def test_source_and_mahler_counters_keep_their_original_units() -> None:
    record = _collect(
        {
            "source_image_adapter_registrations": 1,
            "arithmetic_result_publications": 2,
            "mahler_source_composed_image_reads": 3,
            "mahler_associated_action_demands": 4,
        }
    )
    assert record.construction.source_image_adapter_registrations == 1
    assert record.construction.arithmetic_result_publications == 2
    assert record.observations.mahler_source_composed_image_reads == 3
    assert record.observations.mahler_associated_action_demands == 4


def test_mixed_family_action_work_is_not_folded_into_one_action_count() -> None:
    record = _collect(
        {
            "collatz_physical_action_publications": 2,
            "antihydra_arithmetic_action_publications": 3,
        }
    )
    assert record.action.publications is None
    assert tuple(work.counter_prefix for work in record.family_work) == (
        "antihydra_arithmetic",
        "collatz_physical",
    )


def test_stream_demand_preserves_emission_and_retained_frame_peak_units() -> None:
    record = _collect(
        {
            "recursive_output_stream_requests": 2,
            "recursive_output_stream_node_visits": 10,
            "recursive_output_stream_boundary_evaluations": 3,
            "recursive_output_stream_emitted_digits": 17,
            "recursive_output_stream_frame_peak": 6,
            "temporal_point_requests": 1,
            "temporal_length_requests": 0,
            "arithmetic_returns": 8,
            "physical_roof_evaluations": 0,
            "query_observer_reuses": 1,
            "higher_concrete_operation_evaluations": 0,
            "higher_action_continuation_requests": 0,
        }
    )
    assert record.stream.requests == 2
    assert record.stream.node_visits == 10
    assert record.stream.boundary_evaluations == 3
    assert record.stream.emitted == 17
    assert record.stream.frame_peak == 6
    assert record.demand.point_requests == 1
    assert record.demand.length_requests == 0
    assert record.observations.arithmetic_returns == 8
    assert record.observations.physical_roof_evaluations == 0
    assert record.observations.query_observer_reuses == 1
    assert record.observations.higher_concrete_operation_evaluations == 0
    assert record.construction.postorder_frames is None


def test_malformed_or_unbalanced_snapshot_fails_instead_of_defaulting_to_zero() -> None:
    with pytest.raises(ValueError, match="nonnegative counters"):
        _collect({"source_image_publications": -1})
    with pytest.raises(ValueError, match="do not reconcile"):
        _collect(
            {
                "source_image_publications": 1,
                "source_image_origin_publications": 2,
                "source_image_application_publications": 0,
            }
        )


def test_public_collector_exposes_schema_eight_without_executing_a_query() -> None:
    ledger = ResourceLedger()
    before = ledger.snapshot()
    report = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    assert (
        report.metrics_schema_version == report.temporal_diagnostics.schema_version == 8
    )
    assert report.temporal_diagnostics.resources.audit_complete
    assert report.temporal_diagnostics.construction.postorder_frames is None


def test_warm_source_image_requests_record_hits_without_new_publications() -> None:
    from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )

    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 16)
    before = collect_ledger_metrics(ledger).temporal_diagnostics
    assert workspace._action(16) == workspace.root_action
    demand = SourceImageDemand("physical-summary")
    assert (
        workspace.scheduler.source_image_demanded(
            workspace, workspace.root_source, workspace.root_action, demand
        )
        == workspace.root_image
    )
    workspace.scheduler.source_projection(workspace, workspace.root_image, demand)
    after = collect_ledger_metrics(ledger).temporal_diagnostics
    assert before.action.requests is not None
    assert before.action.exact_hits is not None
    assert after.action.requests == before.action.requests + 2
    assert after.action.exact_hits == before.action.exact_hits + 2
    assert after.action.publications == before.action.publications
    assert before.application.requests is not None
    assert before.application.exact_hits is not None
    assert after.application.requests == before.application.requests + 1
    assert after.application.exact_hits == before.application.exact_hits + 1
    assert after.application.publications == before.application.publications
    assert before.projection.requests is not None
    assert before.projection.exact_hits is not None
    assert after.projection.requests == before.projection.requests + 1
    assert after.projection.exact_hits == before.projection.exact_hits + 1
    assert after.projection.publications == before.projection.publications


def test_reverse_point_and_length_requests_are_measured_at_query_entry() -> None:
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )

    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 2)
    before = collect_ledger_metrics(ledger).temporal_diagnostics
    assert before.demand.point_requests == 0
    assert before.demand.length_requests == 0
    assert workspace.width() > 0
    assert 0 <= workspace.digit(0) <= 9
    after = collect_ledger_metrics(ledger).temporal_diagnostics
    assert after.demand.point_requests == 1
    assert after.demand.length_requests == 1


def test_unobserved_accounting_is_not_a_measured_zero() -> None:
    report = collect_temporal_diagnostics(
        {},
        entries=0,
        nodes=0,
        peak_entries=0,
        peak_nodes=0,
        audit_complete=False,
        accounting_mismatch=None,
    )
    assert report.resources.accounting_mismatch is None
    assert report.resources.audit_complete is False
    with pytest.raises(ValueError, match="accounting measurement"):
        collect_temporal_diagnostics(
            {},
            entries=0,
            nodes=0,
            peak_entries=0,
            peak_nodes=0,
            audit_complete=True,
            accounting_mismatch=None,
        )


def test_snapshot_diagnostics_do_not_walk_inventory_or_semantic_audit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    ledger.bump("collatz_physical_action_publications", 0)
    ledger.bump("collatz_physical_macro_requests", 3)
    before = dict(ledger.counters)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("snapshot-only diagnostics entered an inventory callback")

    monkeypatch.setattr(ResourceLedger, "snapshot", forbidden)
    monkeypatch.setattr(ResourceLedger, "inventory", forbidden)
    report = collect_temporal_diagnostics_snapshot(ledger)
    assert ledger.counters == before
    assert report.family_work[0].macro_requests == 3
    assert report.resources.audit_complete is False
    assert report.resources.accounting_mismatch is None
    assert report.reporting.captured_counter_items == len(before)
    assert report.reporting.projected_counter_items == len(before)
    assert report.reporting.inspected_inventory_rows == 0
    assert report.reporting.captured_mapping_bytes is not None
    assert report.reporting.captured_mapping_bytes > 0


def test_comma_metrics_separate_represented_time_from_work() -> None:
    record = _collect(
        {
            "comma_work": 12,
            "comma_represented_transitions": 10_000_000,
            "comma_phase_cycles": 1_000_000,
            "comma_child_candidate_checks": 9,
            "comma_operand_bit_work": 600,
            "comma_scalar_seam_steps": 1,
            "comma_certificate_work": 0,
        }
    )
    assert record.comma.operations == 12
    assert record.comma.represented_transitions == 10_000_000
    assert record.comma.represented_phase_cycles == 1_000_000
    assert record.comma.child_candidate_checks == 9
    assert record.comma.operand_bits == 600
    assert record.comma.seam_steps == 1
    assert record.comma.certificate_operations == 0
    assert record.action.exact_hits is None
    assert _collect({}).comma.represented_transitions is None


def test_comma_action_reuse_uses_the_common_lane() -> None:
    record = _collect(
        {
            "comma_action_requests": 4,
            "comma_action_hits": 2,
            "comma_action_misses": 2,
            "comma_action_publications": 2,
            "comma_operand_bit_work": 120,
        }
    )
    assert record.action.requests == 4
    assert record.action.exact_hits == 2
    assert record.action.misses == record.action.publications == 2
    assert record.family_work[0].operand_bits == (("comma_operand_bit_work", 120),)
