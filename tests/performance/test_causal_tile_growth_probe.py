"""Causal growth evidence remains cold, unit-separated, and fail-closed."""

from dataclasses import replace

import pytest

from devtools.benchmarks.causal_tile_growth_probe import (
    CausalGrowthRow,
    cold_row,
    cold_rows,
    run_probe,
    series_report,
)


def _row(steps: int, width: int, work: int) -> CausalGrowthRow:
    return CausalGrowthRow(
        scenario="synthetic",
        temporal_steps=steps,
        spatial_width=width,
        coordinate=0,
        temporal_exponent=steps.bit_length() - 1,
        spatial_exponent=width.bit_length() - 1,
        action_physical_ticks=steps,
        digit=0,
        setup_seconds=0.0,
        observation_seconds=0.0,
        diagnostics_seconds=0.0,
        cold_seconds=0.0,
        causal_accounting_version=1,
        causal_frames=work,
        task_memo_evaluations=work,
        task_memo_hits=0,
        primitive_emits=work,
        finite_pair_transfers=0,
        finite_transfer_parent_observations=0,
        result_evaluations=work,
        result_hits=0,
        midpoint_reuse=0,
        demand_descents=1,
        workspace_peak_slots=1,
        boundary_output_requests=work,
        boundary_output_hits=0,
        boundary_output_evaluations=work,
        boundary_output_completions=work,
        boundary_output_failures=0,
        boundary_requested_extent=work,
        boundary_cached_extent=0,
        boundary_output_piece_normalizations=work,
        spatial_buffer_allocations=1,
        spatial_buffer_allocated_bytes=64,
        spatial_buffer_appends=work,
        spatial_buffer_reversal_visits=work,
        spatial_buffer_live_slots=0,
        spatial_buffer_live_bytes=0,
        spatial_buffer_peak_slots=work,
        spatial_buffer_peak_bytes=64,
        boundary_transfer_requests=work,
        boundary_transfer_frames=work,
        boundary_transfer_parent_observations=work,
        boundary_transfer_descents=work,
        boundary_transfer_workspace_peak=work,
        directed_transfer_requests=work,
        directed_transfer_early_hits=0,
        directed_transfer_publication_requests=work,
        directed_transfer_publications=work,
        directed_transfer_late_duplicates=0,
        directed_transfer_leaf_evaluations=work,
        directed_transfer_parent_evaluations=work,
        directed_transfer_workspace_peak=work,
        causal_frame_publications=work,
        causal_frame_payload_reference_publications=work,
        causal_frame_peak_slots=work,
        completed_result_port_validation_requests=work,
        completed_result_port_validation_visits=work,
        directed_transfer_validation_requests=work,
        directed_transfer_validation_visits=work,
        action_nodes=steps.bit_length(),
        action_composition_entries=steps.bit_length(),
        completed_result_entries=work,
        directed_transfer_entries=work,
        causal_interface_entries=work,
        powered_interface_entries=work,
        fused_interface_entries=work,
        spatial_interface_entries=work,
        other_result_memo_entries=0,
        canonical_tile_nodes=work,
        retained_entries=work,
        retained_nodes=work,
        peak_entries=work,
        peak_nodes=work,
        semantic_contract_classes=1,
        temporal_edge_classes=1,
        retained_spatial_interval_bindings=work,
        retained_spatial_interval_union_cells=work,
        sequential_generation_advances=0,
        whole_word_sweeps=0,
        whole_word_symbol_visits=0,
        proof_machine_applications=0,
    )


def test_incomplete_series_is_red_without_inventing_envelopes() -> None:
    report = series_report((_row(4, 8, 5),), (4, 8), axis="temporal_steps")
    assert report["status"] == "RED"
    assert report["measurements_complete"] is False
    assert report["release_blockers"] == ["measurement_series_incomplete"]
    assert all(value is None for value in report["doubling_envelopes"].values())
    assert report["logarithmic_execution_claim"] is False
    assert "retained application result keys only" in report["interval_union_scope"]


def test_pre_behavior_samples_do_not_invent_zero_classification_work() -> None:
    row = _row(4, 8, 5)
    assert row.future_behavior_refinement_observation_checks is None
    report = series_report((row, _row(8, 8, 6)), (4, 8), axis="temporal_steps")
    assert (
        report["doubling_envelopes"]["future_behavior_refinement_observation_checks"]
        is None
    )


def test_work_and_space_envelopes_are_independent_raw_units() -> None:
    rows = tuple(
        replace(
            _row(steps, 8, steps * steps),
            canonical_tile_nodes=2 * steps,
            retained_nodes=3 * steps,
        )
        for steps in (4, 8, 16)
    )
    report = series_report(rows, (4, 8, 16), axis="temporal_steps")
    assert report["status"] == "RED"
    assert report["doubling_envelopes"]["causal_frames"] is False
    assert report["doubling_envelopes"]["canonical_tile_nodes"] is True
    first = report["raw_work_growth"]["causal_frames"][0]
    assert first == {
        "previous_axis": 4,
        "current_axis": 8,
        "previous": 16,
        "current": 64,
        "increment": 48,
        "twice_previous_excess": 32,
    }


def test_forbidden_execution_blocks_an_otherwise_bounded_sample() -> None:
    rows = (
        _row(4, 8, 2),
        replace(_row(8, 8, 3), sequential_generation_advances=1),
    )
    report = series_report(rows, (4, 8), axis="temporal_steps")
    assert report["status"] == "RED"
    assert "forbidden_execution_work_observed" in report["release_blockers"]


def test_cold_rows_use_distinct_indexes_and_report_real_causal_work() -> None:
    rows = cold_rows(
        (
            ("fixed-width", 4, 4, 1),
            ("fixed-width", 8, 4, 1),
        )
    )
    assert [row.temporal_steps for row in rows] == [4, 8]
    assert all(
        row.causal_frames > 0 and row.semantic_contract_classes > 0 for row in rows
    )
    assert all(row.sequential_generation_advances == 0 for row in rows)
    assert all(row.boundary_output_evaluations > 0 for row in rows)
    assert all(row.spatial_buffer_allocations > 0 for row in rows)
    assert all(row.spatial_buffer_live_slots == 0 for row in rows)
    assert all(row.spatial_buffer_live_bytes > 0 for row in rows)
    assert all(
        row.cold_seconds >= row.setup_seconds + row.observation_seconds for row in rows
    )
    assert all(
        row.spatial_buffer_peak_bytes >= row.spatial_buffer_live_bytes for row in rows
    )


@pytest.mark.parametrize(
    ("steps", "width", "coordinate"),
    ((True, 4, 0), (4, True, 0), (4, 4, True), (0, 4, 0), (4, 3, 0)),
)
def test_cold_probe_rejects_numeric_aliases_and_invalid_axes(
    steps: int,
    width: int,
    coordinate: int,
) -> None:
    with pytest.raises(ValueError):
        cold_row(
            "fixed-width",
            steps,
            width,
            coordinate=coordinate,
        )


@pytest.mark.parametrize("axis", ((4, 6), (4, True), (4, 0)))
def test_series_probe_rejects_non_power_of_two_axis_domains(
    axis: tuple[int, int],
) -> None:
    with pytest.raises(ValueError):
        run_probe(temporal_steps=axis, spatial_widths=(4, 8))


def test_versioned_missing_counters_are_unavailable_instead_of_zero() -> None:
    rows = (
        replace(
            _row(4, 8, 2),
            causal_accounting_version=0,
            boundary_output_requests=None,
            boundary_output_hits=None,
            boundary_output_failures=None,
        ),
        replace(
            _row(8, 8, 3),
            causal_accounting_version=0,
            boundary_output_requests=None,
            boundary_output_hits=None,
            boundary_output_failures=None,
        ),
    )
    report = series_report(rows, (4, 8), axis="temporal_steps")
    assert report["status"] == "RED"
    assert report["raw_work_growth"]["boundary_output_requests"][0]["current"] is None
    assert (
        "boundary_output_requests_measurement_unavailable" in report["release_blockers"]
    )


def test_growing_reverse_axis_counts_normalized_generation_exactly() -> None:
    row, _ledger = cold_row("growing-196", 2, 8, coordinate=0)
    assert row.action_physical_ticks == 1
    assert row.digit == 5  # 196 -> 887 -> 1675
    assert row.setup_seconds > 0
    assert row.observation_seconds > 0
    assert row.diagnostics_seconds >= 0
