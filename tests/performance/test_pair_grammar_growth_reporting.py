"""Research measurements must expose historical construction and replay."""

import pytest

from devtools.benchmarks.field_image_growth_probe import (
    research_event_measurement,
    research_pair_measurement,
)
from tests.support.report_values import object_record


@pytest.mark.parametrize(
    ("seed", "horizon", "value"),
    ((1, 0, "1"), (1, 6, "154"), (196, 20, "70446464506")),
)
def test_pair_probe_measures_cold_construction_separately(
    seed: int, horizon: int, value: str
) -> None:
    result = research_pair_measurement(seed, horizon)
    assert result["value"] == value
    assert result["width"] == len(value)
    assert result["chronological_successors"] == horizon
    assert result["production_cutover_complete"] is False
    assert result["warm_new_nodes"] == 0
    assert type(result["retained_ledger_nodes"]) is int
    counters = object_record(result["construction_counters"])
    assert counters
    if horizon:
        assert counters["reverse_pair_slp_effect_nodes"]
    for key in (
        "construction_seconds",
        "observation_seconds",
        "rendering_seconds",
        "reference_seconds",
        "warm_last_demand_seconds",
    ):
        assert type(result[key]) is float


@pytest.mark.parametrize("horizon", (-1, 1025, True))
def test_pair_probe_cannot_expand_unbounded_research_history(horizon: int) -> None:
    with pytest.raises(ValueError, match="horizon"):
        research_pair_measurement(196, horizon)


@pytest.mark.parametrize("seed", (1, 196))
def test_direct_event_probe_reports_discovery_without_claiming_temporal_cutover(
    seed: int,
) -> None:
    result = research_event_measurement(seed, 20)
    assert result["chronological_successors"] == 20
    assert result["production_cutover_complete"] is False
    counters = object_record(result["construction_counters"])
    assert counters["carry_event_reset_events"]
    assert counters["carry_event_domain_actions"]
    assert "live_carry_input_nodes" not in counters
    assert "reverse_centered_future_slp_nodes" not in counters
    for key in (
        "construction_seconds",
        "observation_seconds",
        "rendering_seconds",
        "reference_seconds",
    ):
        assert type(result[key]) is float
    assert type(result["retained_innovation_nodes"]) is int
