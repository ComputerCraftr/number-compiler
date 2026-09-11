from devtools.benchmarks.nth_projection_probe import MAX_DOUBLING_RATIO, run_probe
import pytest


@pytest.mark.validation  # Maintained cross-family execution-scaling benchmark.
def test_nth_projection_work_stays_well_below_quadratic_doubling() -> None:
    result = run_probe()
    assert result["status"] == "PASS"
    assert result["max_doubling_ratio"] < MAX_DOUBLING_RATIO < 4.0
    assert result["special"]["fermat"]["raw_squarings"] == 0
    assert result["special"]["mersenne"]["raw_squarings"] == 0
