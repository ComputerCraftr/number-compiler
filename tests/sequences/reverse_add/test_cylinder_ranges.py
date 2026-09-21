"""Parametric geometry and source-bound interval ports, not temporal NF."""

from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn
from number_compiler.arithmetic.contracts.cylinder_chart import (
    CylinderChart,
    right_dyadic_blocks,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.sequences.reverse_add.test_source_ports import (
    _pairs,
    _source,
    _step_digits,
)


def test_chart_fusion_and_interval_images_in_one_guard_environment() -> None:
    charts = (
        CylinderChart(),
        CylinderChart(-1, -1, 1, 1),
        CylinderChart(1, 3, -1, 2),
        CylinderChart(-1, 8, 0, -1),
    )
    for a, b, extent, growth in product(charts, charts, (0, 3, 10), (0, 1, 2)):
        fused = a.then(b)
        for i in range(-3, 12):
            assert fused.slope * i + fused.shift(extent, growth) == (
                b.slope * (a.slope * i + a.shift(extent, growth))
                + b.shift(extent, growth)
            )
        low, high = fused.image(-3, 12, extent, growth)
        assert set(range(low, high)) == {
            fused.slope * i + fused.shift(extent, growth) for i in range(-3, 12)
        }
    reflection = CylinderChart(-1, -1, 1, 1)
    assert reflection.then(reflection) == CylinderChart()
    assert reflection.image(3, 3, 10, 1)[0] == reflection.image(3, 3, 10, 1)[1]
    for a, b, c in product(charts, repeat=3):
        assert a.then(b).then(c) == a.then(b.then(c))


def test_dyadic_restriction_cover_is_exact_aligned_and_bounded() -> None:
    for start in range(64):
        for stop in range(start, 65):
            blocks = tuple(right_dyadic_blocks(start, stop))
            end = stop
            for position, span in blocks:
                assert span > 0 and span & (span - 1) == 0
                assert position % span == 0
                assert position + span == end
                end = position
            assert end == start
            assert len(blocks) <= 2 * stop.bit_length()
    # This must visit fragments, not enumerate coordinates or allocate a field.
    blocks = tuple(right_dyadic_blocks(17, (1 << 512) - 19))
    assert len(blocks) <= 1024


@pytest.mark.parametrize("seed", (0, 1, 19, 89, 196, 1001, 12003))
def test_both_layers_oriented_ranges_match_independent_literal_folds(seed: int) -> None:
    source = _source(seed, 10)
    ports = SourceCarryPorts(source, ResourceLedger())
    for layer, digits in ((1, source.digits), (2, _step_digits(source.digits, 10))):
        pairs = _pairs(digits)
        extent = len(pairs)
        for start in range(extent + 1):
            for stop in range(start, extent + 1):
                for reverse in (False, True):
                    chart = (
                        CylinderChart(-1, extent - 1) if reverse else CylinderChart()
                    )
                    actual = ports.range_transfer(layer, start, stop, chart)
                    positions = range(start, stop)
                    for incoming in (0, 1):
                        expected = incoming
                        for i in positions:
                            j = extent - 1 - i if reverse else i
                            expected = int(pairs[j] + expected >= 10)
                        assert apply_carry_fn(actual, incoming) == expected
        # Growth stays a chart parameter; it is not an eagerly split source tree.
        reflected = CylinderChart(-1, -1, 1, 1)
        assert ports.range_transfer(layer, 0, extent, reflected) == (
            ports.range_transfer(layer, 0, extent)
        )
    ports.dispose()


def test_translated_reflected_subrange_preserves_orientation() -> None:
    ports = SourceCarryPorts(_source(4590, 10), ResourceLedger())
    # Pair field (4,14,14,4): forward [0,2) resets to 1; its reverse resets to 0.
    assert ports.range_transfer(1, 0, 2) is CarryFn.CONST1
    assert ports.range_transfer(1, 0, 2, CylinderChart(-1, 1)) is CarryFn.CONST0
    assert ports.range_transfer(1, -2, 0, CylinderChart(1, 2)) is CarryFn.CONST1


def test_whole_admitted_child_and_reflection_reuse_its_summary(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = _source(int("4" * 256 + "5" * 256), 10)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    assert ports.range_transfer(1, 0, 512) is CarryFn.ID
    before = ledger.snapshot()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("an admitted whole interval descended into source points")

    monkeypatch.setattr(SourceCarryPorts, "_raw_first_pair", forbidden)
    assert ports.range_transfer(1, 0, 512) is CarryFn.ID
    assert ports.range_transfer(1, 0, 512, CylinderChart(-1, -1, 1)) is CarryFn.ID
    assert ports.range_transfer(1, 128, 384) is CarryFn.ID
    assert (
        ledger.counters["reverse_source_ports_postorder_frames"]
        == (before.counters["reverse_source_ports_postorder_frames"])
    )
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)


def test_ranges_reject_invalid_geometry_and_unadmitted_time_before_source_work() -> (
    None
):
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_source(196, 10), ledger)
    before = ledger.counters.get("reverse_source_ports_source_reads", 0)
    with pytest.raises(ValueError, match="layers"):
        ports.range_transfer(4, 0, 1)
    with pytest.raises(ValueError, match="reversed"):
        ports.range_transfer(2, 2, 1)
    with pytest.raises(TypeError, match="exact integers"):
        ports.range_transfer(2, False, 1)
    with pytest.raises(IndexError):
        ports.range_transfer(1, 0, 4)
    assert ledger.counters.get("reverse_source_ports_source_reads", 0) == before
    assert ports.range_transfer(1, 1, 1) is CarryFn.ID
    ports.dispose()
    with pytest.raises(ValueError, match="disposed"):
        ports.range_transfer(1, 0, 1)
