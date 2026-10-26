"""Matrix benchmarks use registry coordinates and preserve real CLI evidence."""

import pytest

from devtools.benchmarks.temporal_matrix_cli_comparison import compare_matrix_routes


@pytest.mark.parametrize("family,index", [("antihydra", 16), ("fermat", 3)])
def test_matrix_comparison_uses_family_coordinate_and_clock(
    family: str, index: int
) -> None:
    rows = compare_matrix_routes(family, 196, index, (2,), 1)
    assert rows
    assert {row["mode"] for row in rows} == {"cold", "warm", "bypass"}
    assert all(row["exit_code"] == 0 for row in rows)
    for row in rows:
        packet = row["packet"]
        assert row["clock_unit"] in {
            "physical-recurrence-ticks",
            "ordinary-tripling-ticks",
        }
        assert packet["execution_authority"] is False
        assert packet["source_index"] == index
        assert row["horizon_ticks"] == 2
        assert row["endpoint_facts"]


def test_matrix_benchmark_rejects_unadmitted_horizons() -> None:
    with pytest.raises(ValueError, match="family admission"):
        compare_matrix_routes("antihydra", 196, 16, (33,), 1)
