"""Public cache measurements distinguish aliases from certified action IDs."""

import pytest

from devtools.benchmarks.clock_key_growth_probe import measure


@pytest.mark.parametrize("family", ("196", "collatz"))
def test_clock_audit_keeps_live_context_and_measures_warm_cache(family: str) -> None:
    row = measure(family, 8)
    warm = row["warm_delta"]
    assert isinstance(warm, dict)
    assert warm["point_response_cache_hits"] == 1
    assert warm["point_response_evaluations"] == 0
    assert warm["completed_result_entries"] == 0
    assert warm["tile_scheduler_leaf_function_applications"] == 0
    ablations = row["key_ablations"]
    assert isinstance(ablations, dict)
    assert ablations["production_clock_action_interner_present"] is False
    projections = ablations["projections"]
    assert isinstance(projections, dict)
    full = projections["full_key"]
    assert full["conflicted_fibers"] == 0
    assert full["potential_key_aliases"] == 0
    assert projections["finite_contract_only"]["conflicted_fibers"] > 0
    assert all(not row["promotion_certified"] for row in projections.values())
