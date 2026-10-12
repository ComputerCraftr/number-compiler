"""Differential checks for the runtime Entry/Near chart against literal children.

The oracle follows actual decimal children and only skips an Entry run after
checking one complete literal phase and its last candidate phase. It does not
call the chart transition or the production sector-child classifier.
"""

from __future__ import annotations

from math import gcd

from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    ChartMove,
    chart_moves,
)
from tests.support.comma_oracles import literal_children, literal_phase_jump


def _value(chart: BoundaryChart, exponent: int) -> int:
    scale: int = 10 ** (exponent + chart.delta)
    if chart.kind == "entry":
        return chart.leading * scale + chart.coordinate
    return (chart.leading + 1) * scale - chart.coordinate


def _ticks(move: ChartMove, exponent: int) -> int:
    weight = move.weight
    numerator: int = (
        weight.scale * 10 ** (exponent + weight.exponent_delta) + weight.offset
    )
    ticks, remainder = divmod(numerator, weight.denominator)
    assert remainder == 0
    return ticks


def _assert_move_matches_literal_children(
    chart: BoundaryChart, move: ChartMove, exponent: int
) -> None:
    source = _value(chart, exponent)
    ticks = _ticks(move, exponent)

    if chart.kind == "entry":
        target, literal_ticks = literal_phase_jump(source)
        assert literal_ticks > 0
        assert move.next_chart is not None
        assert move.terminal_chart is None
        assert move.cycle is not None
        assert ticks == literal_ticks
        assert _value(move.next_chart, exponent) == target
        assert move.cycle.leading == chart.leading
        assert move.cycle.entering_digit == source % 10
        assert move.cycle.period == 10 // gcd(chart.leading, 10)
        return

    children = literal_children(source)
    if move.next_chart is None:
        assert move.terminal_chart == chart
        assert ticks == 0
        assert not move.literal_increment
        if move.fork_a is None:
            assert children == ()
        else:
            scale: int = 10 ** (exponent + chart.delta)
            assert children == (move.fork_a * scale - 1, move.fork_a * scale)
        return

    assert move.cycle is None
    assert ticks > 0
    cursor = source
    increment = 0
    for _ in range(ticks):
        next_children = literal_children(cursor)
        assert len(next_children) == 1
        successor = next_children[0]
        increment += successor - cursor
        cursor = successor
    assert cursor == _value(move.next_chart, exponent)
    assert increment == move.literal_increment


def test_scalar_initial_chart_step_matches_literal_model_for_every_phase() -> None:
    """Exercise every admitted N/Z start and all 924 first-step phases."""
    for kind in ("N", "Z"):
        for leading in range(2, 10):
            for residue in range(PERIOD):
                exponent = residue if residue >= 5 else residue + PERIOD
                chart, move = next(chart_moves(kind, leading, residue))
                _assert_move_matches_literal_children(chart, move, exponent)


def test_complete_scalar_and_grouped_walks_match_literal_model() -> None:
    """Both runtime modes terminate with the literal-oracle return fields."""
    residues = (0, 1, 4, 5, 10, 11, 461, 923)
    for kind in ("N", "Z"):
        for leading in range(2, 10):
            for residue in residues:
                exponent = residue if residue >= 5 else residue + PERIOD
                for grouped_near in (False, True):
                    terminal_seen = False
                    for chart, move in chart_moves(
                        kind, leading, residue, grouped_near=grouped_near
                    ):
                        assert not terminal_seen
                        _assert_move_matches_literal_children(chart, move, exponent)
                        if move.next_chart is None:
                            terminal_seen = True
                    assert terminal_seen
