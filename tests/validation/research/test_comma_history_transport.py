"""History erasure checks concern control, not absolute occurrence data."""

from __future__ import annotations

import pytest

from devtools.experiments.comma import generate_rank_candidate as candidates
from number_compiler.sequences.comma.arithmetic import cycle_transfer
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    chart_step,
)


def _normalized_chart(
    residue: int, chart: BoundaryChart | None
) -> tuple[str, int, int, int] | None:
    if chart is None:
        return None
    return (
        chart.kind,
        chart.leading,
        (residue + chart.delta) % PERIOD,
        chart.coordinate,
    )


@pytest.mark.parametrize("phase", [0, 5, 42, 923])
def test_round_control_preserves_rebased_history(phase: int) -> None:
    for offset in range(91):
        base = candidates._round_close_candidate(
            phase, BoundaryChart("entry", 1, 0, offset)
        )
        for delta in (1, 923, 924, 1848):
            residue = (phase - delta) % PERIOD
            lifted = candidates._round_close_candidate(
                residue, BoundaryChart("entry", 1, delta, offset)
            )
            assert (lifted.kind, lifted.fork_a, lifted.positions) == (
                base.kind,
                base.fork_a,
                base.positions,
            )
            assert _normalized_chart(residue, lifted.terminal_chart) == (
                _normalized_chart(phase, base.terminal_chart)
            )
            assert _normalized_chart(residue, lifted.successor_chart) == (
                _normalized_chart(phase, base.successor_chart)
            )
            assert lifted.terminal_chart.delta == base.terminal_chart.delta + delta


def test_equal_control_does_not_erase_terminal_gain_or_literal_weight() -> None:
    base = candidates._round_close_candidate(5, BoundaryChart("entry", 1, 0, 27))
    lifted = candidates._round_close_candidate(5, BoundaryChart("entry", 1, 924, 27))
    assert base.kind == lifted.kind == "fork"
    assert base.fork_a == lifted.fork_a == 2
    assert base.terminal_chart.delta == 0
    assert lifted.terminal_chart.delta == 924
    assert base.terminal_chart != lifted.terminal_chart
    assert _normalized_chart(5, base.terminal_chart) == _normalized_chart(
        5, lifted.terminal_chart
    )

    first = chart_step(5, BoundaryChart("entry", 1, 0, 3)).weight
    shifted = chart_step(5, BoundaryChart("entry", 1, 924, 3)).weight
    assert first.exponent_delta == 0
    assert shifted.exponent_delta == 924
    first_numerator = first.scale * 10 ** (5 + first.exponent_delta) + first.offset
    shifted_numerator = (
        shifted.scale * 10 ** (5 + shifted.exponent_delta) + shifted.offset
    )
    assert first_numerator % first.denominator == 0
    assert shifted_numerator % shifted.denominator == 0
    assert first_numerator // first.denominator < (
        shifted_numerator // shifted.denominator
    )


def test_internal_entry_catalog_includes_offsets_through_98() -> None:
    periods, decade_classes = candidates.phase_factorization_profile()
    assert sum(periods.values()) == 116
    assert decade_classes == 6454
    assert (
        sum(
            periods[cycle_transfer(leading, offset % 10).displacement]
            for leading in range(1, 10)
            for offset in range(99)
        )
        == 7019
    )
