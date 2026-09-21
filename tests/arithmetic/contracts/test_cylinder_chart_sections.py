import pytest

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart


@pytest.mark.parametrize("slope", [-1, 1])
@pytest.mark.parametrize("lane", [0, 1])
def test_section_transport_preserves_signed_coordinates(slope: int, lane: int) -> None:
    for offset in (-17, -4, -1, 0, 1, 4, 17):
        for extent, growth in ((0, 0), (3, 0), (3, 1), (10**30, 10**20 + 1)):
            chart = CylinderChart(slope, offset, -1, 3)
            selected, result = chart.cartier_section(lane, extent=extent, growth=growth)
            assert selected in (0, 1)
            assert result.extent_scale == result.growth_scale == 0
            for coordinate in (-101, -1, 0, 1, 101):
                original = slope * (2 * coordinate + lane) + chart.shift(extent, growth)
                transported = 2 * (result.slope * coordinate + result.offset) + selected
                assert original == transported


def test_reflection_uses_floor_and_opposite_parity() -> None:
    # R_0(2*i+1) = -2*i-1 = 2*(-i-1)+1, not 2*(-i)+1.
    assert CylinderChart(-1).cartier_section(1, extent=0, growth=0) == (
        1,
        CylinderChart(-1, -1),
    )


def test_sections_commute_with_chronological_index_composition() -> None:
    charts = (
        CylinderChart(),
        CylinderChart(-1, -1, 1, 1),
        CylinderChart(1, -7, 2, -1),
        CylinderChart(-1, 3, -1, 2),
    )
    for first in charts:
        for second in charts:
            for lane in (0, 1):
                first_lane, first_chart = first.cartier_section(
                    lane, extent=13, growth=2
                )
                second_lane, second_chart = second.cartier_section(
                    first_lane, extent=13, growth=2
                )
                assert first.then(second).cartier_section(
                    lane, extent=13, growth=2
                ) == (second_lane, first_chart.then(second_chart))


def test_growth_environment_changes_the_reflected_section() -> None:
    reflection = CylinderChart(-1, -1, 1, 1)
    assert reflection.cartier_section(0, extent=3, growth=0) == (
        0,
        CylinderChart(-1, 1),
    )
    assert reflection.cartier_section(0, extent=3, growth=1) == (
        1,
        CylinderChart(-1, 1),
    )


@pytest.mark.parametrize("lane", [-1, 2, 100])
def test_section_rejects_invalid_lanes(lane: int) -> None:
    with pytest.raises(ValueError, match="lane"):
        CylinderChart().cartier_section(lane, extent=1, growth=0)


def test_section_rejects_boolean_lane_and_negative_environment() -> None:
    with pytest.raises(TypeError, match="exact integer"):
        CylinderChart().cartier_section(True, extent=1, growth=0)
    with pytest.raises(ValueError, match="nonnegative"):
        CylinderChart().cartier_section(0, extent=-1, growth=0)
