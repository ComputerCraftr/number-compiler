"""Growth gates count work and retained populations in their own units."""

import pytest

from devtools.benchmarks.reverse_temporal_power_probe import doubling_envelope


def test_thousands_of_canonical_nodes_may_have_linear_growth() -> None:
    rows = [
        {"generation": generation, "nodes": 700 * generation + 300}
        for generation in (16, 32, 64, 128, 256)
    ]
    assert doubling_envelope(rows, "nodes")


def test_small_image_graph_does_not_mask_quadratic_projection_or_memos() -> None:
    rows = [
        {
            "generation": generation,
            "images": 2 * generation.bit_length() + 3,
            "work": generation * generation,
            "memo_slots": generation * generation // 2,
        }
        for generation in (16, 32, 64, 128, 256)
    ]
    assert doubling_envelope(rows, "images")
    assert not doubling_envelope(rows, "work")
    assert not doubling_envelope(rows, "memo_slots")


@pytest.mark.parametrize("rows", ([], [{"generation": 16, "work": 2}]))
def test_growth_requires_more_than_one_completed_observation(
    rows: list[dict[str, object]],
) -> None:
    assert not doubling_envelope(rows, "work")


def test_growth_rejects_an_incomplete_doubling_series() -> None:
    rows = [{"generation": 16, "work": 200}, {"generation": 64, "work": 250}]
    assert not doubling_envelope(rows, "work")
