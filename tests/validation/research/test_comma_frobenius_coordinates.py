"""Finite differential evidence for diagonal coordinates, not safety proofs."""

from math import gcd
from typing import cast

import pytest

from devtools.experiments.comma.temporal_masks import (
    FrobeniusClock,
    entry_diagonal_headroom,
    frobenius_entry,
    offset_orbit,
)
from number_compiler.sequences.comma.arithmetic import (
    cycle_residue_period,
    cycle_transfer,
    phase_prefix_displacement,
)
from number_compiler.sequences.comma.boundary_chart import BoundaryChart, chart_step


def _near_endpoint(leading: int, headroom: int) -> BoundaryChart:
    chart = BoundaryChart("near", leading, 0, headroom)
    period = cycle_transfer(leading, (-headroom) % 10).period
    for _ in range(period + 1):
        move = chart_step(5, chart)
        if move.next_chart is None:
            assert move.terminal_chart is not None
            return move.terminal_chart
        chart = move.next_chart
        if chart.kind == "entry":
            return chart
    raise AssertionError("Near response exceeded a local digit orbit")


def test_crt_projection_and_advance_match_scalar_clock() -> None:
    displacements = {
        cycle_transfer(f, d).displacement for f in range(1, 10) for d in range(10)
    }
    clocks = set()
    for residue in range(924):
        clock = FrobeniusClock.from_residue(residue)
        clocks.add(clock)
        assert clock.advance() == FrobeniusClock.from_residue((residue + 1) % 924)
        for displacement in displacements:
            expected = (residue - 5) % cycle_residue_period(displacement)
            assert clock.short_phase(displacement) == expected
    assert len(clocks) == 924


def test_diagonal_occurrence_lift_preserves_exact_chart_and_weight() -> None:
    controls = set()
    weights: dict[tuple[int, int, int], set[tuple[int, int, int]]] = {}
    for f in range(1, 10):
        for x in range(99):
            transfer = cycle_transfer(f, x % 10)
            for phase in range(cycle_residue_period(transfer.displacement)):
                exponent = 5 + phase
                power = pow(10, exponent, transfer.displacement)
                minimum = 1 + int(f < 9)
                expected = minimum + (power - x - minimum) % transfer.displacement
                entry = frobenius_entry(f, x, FrobeniusClock.from_residue(exponent))
                controls.add(entry.control_id)
                assert entry.headroom == expected
                assert _near_endpoint(f, entry.headroom) == _near_endpoint(
                    f, entry.canonical_headroom
                )
                assert (
                    entry_diagonal_headroom(f, x, power, transfer.displacement)
                    == expected
                )
                move = chart_step(exponent, BoundaryChart("entry", f, 0, x))
                weights.setdefault(entry.control_id, set()).add(
                    (move.weight.scale, move.weight.offset, move.weight.denominator)
                )
                assert move.next_chart == BoundaryChart("near", f, 0, expected)
                literal_source = f * 10**exponent + x
                literal_endpoint = (f + 1) * 10**exponent - expected
                difference = literal_endpoint - literal_source
                assert difference % transfer.displacement == 0
                expected_weight = difference // transfer.displacement * transfer.period
                numerator = move.weight.scale * 10**exponent + move.weight.offset
                assert numerator // move.weight.denominator == expected_weight
                assert numerator % move.weight.denominator == 0
                if f == 1 and x <= 90:
                    assert entry.deck == offset_orbit(x)
    # Coverage count concerns only this finite domain; it proves no closure.
    assert len(controls) == 450
    # Endpoint conjugacy must never be used as an equal-weight assertion.
    assert any(len(occurrences) > 1 for occurrences in weights.values())


def test_digit_potential_and_deck_are_preserved_by_literal_orbit_step() -> None:
    clock = FrobeniusClock.from_residue(23)
    for f in range(1, 10):
        for x in range(99):
            entry = frobenius_entry(f, x, clock)
            successor = frobenius_entry(f, x + 10 * (x % 10) + f, clock)
            assert entry.deck == successor.deck
            assert entry.control_id == successor.control_id
            assert entry.orbit == x % gcd(f, 10)
            assert (
                entry.orbit_displacement - x % 10 + entry.orbit == 10 * entry.potential
            )
            if f == 1:
                assert entry.potential == entry.position * (entry.position - 1) // 2


def test_local_control_key_does_not_erase_receiving_clock() -> None:
    first_clock = FrobeniusClock.from_residue(1)
    second_clock = FrobeniusClock.from_residue(23)
    first = frobenius_entry(1, 0, first_clock)
    second = frobenius_entry(1, 0, second_clock)
    assert first.control_id == second.control_id == (1, 0, 22)
    target = _near_endpoint(1, first.headroom)
    assert target == _near_endpoint(1, second.headroom)
    assert target == BoundaryChart("entry", 2, 0, 49)
    assert frobenius_entry(2, 49, first_clock).innovation == 0
    assert frobenius_entry(2, 49, second_clock).innovation == 24


def test_canonical_headroom_is_not_an_occurrence_headroom() -> None:
    entry = frobenius_entry(1, 1, FrobeniusClock.from_residue(0))
    assert entry.canonical_headroom == 300
    assert entry.headroom == 299
    assert entry.orbit_displacement == 1
    assert _near_endpoint(1, entry.headroom) == _near_endpoint(
        1, entry.canonical_headroom
    )


@pytest.mark.parametrize(
    "args",
    [(0, 0, 0, 460), (1, -1, 0, 460), (1, 0, 1, 460), (1, 0, 0, "460")],
)
def test_diagonal_rejects_invalid_coordinates(args: tuple[object, ...]) -> None:
    with pytest.raises(ValueError):
        entry_diagonal_headroom(*cast(tuple[int, int, int, int], args))


def test_closed_complete_cycles_match_independent_literal_sum() -> None:
    for f in range(1, 10):
        for digit in range(10):
            period = 10 // gcd(f, 10)
            for steps in range(2 * period + 3):
                expected = sum(10 * ((digit + i * f) % 10) + f for i in range(steps))
                assert phase_prefix_displacement(f, digit, steps) == expected
