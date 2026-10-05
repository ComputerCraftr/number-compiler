"""Do not confuse finite scheduler evaluations with temporal trajectory replay."""

from dataclasses import replace

import pytest

from devtools.benchmarks.tile_projection_accounting import projection_accounting
from number_compiler.resources.metric_records import HashLifeProjectionMetrics


def _row_int(row: dict[str, object], name: str) -> int:
    value = row[name]
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError((name, value))
    return value


def test_scheduler_leaf_work_is_reported_and_retired_work_is_rejected() -> None:
    metrics = HashLifeProjectionMetrics(
        point_queries=0,
        section_requests=0,
        section_cache_hits=0,
        section_cache_entries=0,
        leaf_word_requests=0,
        leaf_word_cache_hits=0,
        leaf_word_cache_entries=0,
        boundary_requests=0,
        boundary_cache_hits=0,
        boundary_cache_entries=0,
        canonical_tile_roots=0,
        retained_execution_nodes=0,
        canonical_program_word_roots=0,
        left_boundary_residuals=0,
        right_boundary_residuals=0,
        bounded_application_enabled=1,
        temporal_leaf_applications=7,
        tile_scheduler_leaf_function_applications=7,
    )
    assert (
        projection_accounting(metrics)["tile_scheduler_leaf_function_applications"] == 7
    )
    # A retired compatibility alias is not the execution authority.
    assert projection_accounting(
        replace(metrics, temporal_leaf_applications=0)
    ) == projection_accounting(metrics)
    for invalid in (
        replace(metrics, sequential_generation_advances=1),
        replace(metrics, higher_concrete_operation_evaluations=1),
        replace(metrics, higher_action_continuation_requests=1),
        replace(metrics, temporal_leaf_diamond_descents=1),
    ):
        with pytest.raises(AssertionError, match="retired-temporal-interpreter"):
            projection_accounting(invalid)


@pytest.mark.validation
@pytest.mark.parametrize("family", ["reverse", "collatz"])
def test_public_probe_reports_current_family_work(
    family: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    if family == "reverse":
        from devtools.benchmarks import reverse_temporal_power_probe as reverse

        monkeypatch.setattr(reverse, "PROJECTION_INDICES", (16,))
        rows = reverse._production_projection_rows()
    else:
        from devtools.benchmarks import collatz_temporal_power_probe as collatz

        monkeypatch.setattr(collatz, "PROJECTION_STEPS", (16,))
        rows = collatz._projection_rows()
    row = rows[0]
    if family == "reverse":
        # The production reverse consumer is now the authenticated source-image
        # projection owner. These checks replace the retired tile-leaf and
        # completed-result-profile assertions without manufacturing equivalent
        # scheduler counts. Keep temporal higher-runtime work visible as a real
        # diagnostic; its acceptance gate lives in the probe report.
        assert _row_int(row, "source_image_publications") > 0
        assert _row_int(row, "source_image_projection_publications") > 0
        assert row["source_image_replay_stable"] is True
        assert row["runtime_image_matches_scalar"] is True
        assert row["resource_accounting_exact"] is True
        assert type(row["higher_concrete_operation_evaluations"]) is int
    else:
        assert _row_int(row, "sequential_generation_advances") == 0
        assert _row_int(row, "explicitly_lowered_digits") == 0
        assert _row_int(row, "source_image_projection_publications") > 0
        assert _row_int(row, "collatz_image_radix_demands") > 0
        assert _row_int(row, "direct_powered_point_queries") == 1
        assert row["runtime_image_matches_scalar"] is True
        assert row["source_image_replay_publications_stable"] is True
        assert row["resource_accounting_exact"] is True
