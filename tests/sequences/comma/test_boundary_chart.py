"""Chart/control regressions independent of finite rank data."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import Literal

import pytest

from number_compiler.sequences.comma import arithmetic, boundary_chart
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    chart_moves,
    chart_step,
    initial_chart,
)
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_macro,
)
from tests.sequences.comma.test_boundary_quotient import _literal_children


def _value(chart: BoundaryChart, exponent: int) -> int:
    scale = int(pow(10, exponent + chart.delta))
    return (
        chart.leading * scale + chart.coordinate
        if chart.kind == "entry"
        else (chart.leading + 1) * scale - chart.coordinate
    )


@pytest.mark.parametrize("a", range(2, 10))
def test_nine_tail_includes_first_literal_edge(a: int) -> None:
    chart = initial_chart("N", a)
    assert chart == BoundaryChart("near", a - 1, 0, 1)
    move = chart_step(10, chart)
    assert move.next_chart == BoundaryChart("entry", a, 0, a + 89)
    assert move.cycle is None
    assert move.weight == boundary_chart.UNIT_WEIGHT
    assert move.literal_increment == a + 90
    assert _literal_children(_value(chart, 10)) == (_value(move.next_chart, 10),)
    macro = construct_macro(BoundaryState("N", a, 10))
    first = macro.sector_fragments[0]
    assert first.literal_steps == 1
    assert first.literal_increment == a + 90
    assert macro.prefix_weights[1].evaluate(10) == 1


@pytest.mark.parametrize("kind", ["N", "Z"])
@pytest.mark.parametrize("exponent", [5, 10, 934])
def test_chart_moves_preserve_weight_endpoint_and_all_children(
    kind: Literal["N", "Z"], exponent: int
) -> None:
    macro = construct_macro(BoundaryState(kind, 2, exponent % 924))
    moves = tuple(chart_moves(kind, 2, exponent % 924))
    assert len(moves) == 1 + sum(
        1 if fragment.period else fragment.literal_steps
        for fragment in macro.sector_fragments
    )
    elapsed = 0
    for chart, move in moves[:-1]:
        assert move.next_chart is not None
        source, target = _value(chart, exponent), _value(move.next_chart, exponent)
        weight = move.weight
        numerator = (
            weight.scale * 10 ** (exponent + weight.exponent_delta) + weight.offset
        )
        ticks, remainder = divmod(numerator, weight.denominator)
        assert remainder == 0 and ticks > 0
        if move.cycle is None:
            assert _literal_children(source) == (target,)
            assert target - source == move.literal_increment
            assert ticks == 1
        else:
            count, remainder = divmod(ticks, move.cycle.period)
            assert remainder == 0
            assert count > 0
            assert ticks == count * move.cycle.period
            assert source + count * move.cycle.displacement == target
            assert source % 10 == target % 10
        assert macro.point(exponent, elapsed) == source
        elapsed += ticks
        assert macro.point(exponent, elapsed) == target
    assert elapsed == macro.weight.evaluate(exponent)
    terminal, last = moves[-1]
    assert last.next_chart is None
    assert last.terminal_chart == terminal
    assert last.weight == boundary_chart.ZERO_WEIGHT
    assert _value(terminal, exponent) == macro.endpoint.evaluate(exponent)
    assert _literal_children(_value(terminal, exponent)) == tuple(
        child.value(exponent + macro.exponent_delta) for child in macro.ordered_children
    )


def test_first_n_boundary_has_93_chart_positions_not_92() -> None:
    moves = tuple(chart_moves("N", 2, 10))
    assert len(moves) == 93
    assert moves[0][0] == BoundaryChart("near", 1, 0, 1)
    assert moves[1][0] == BoundaryChart("entry", 2, 0, 91)
    assert moves[-1][1].fork_a == 7
    assert moves[-1][0].delta == 2


def test_macro_consumes_emitted_weight_instead_of_recomputing_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = boundary_chart.chart_step

    def altered(
        residue: int,
        chart: BoundaryChart,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> boundary_chart.ChartMove:
        assert charge_bits is None
        move = original(residue, chart)
        if chart == initial_chart("N", 2):
            return replace(move, weight=boundary_chart.ChartWeight(0, 0, 2, 1))
        return move

    monkeypatch.setattr(boundary_chart, "chart_step", altered)
    with pytest.raises(AssertionError, match="weight differs"):
        construct_macro(BoundaryState("N", 2, 10))


def test_landmine_retains_its_exact_headroom() -> None:
    chart, move = tuple(chart_moves("N", 3, 5))[-1]
    assert move.next_chart is None and move.fork_a is None
    assert chart.kind == "near" and chart.leading == 9
    assert chart.coordinate == 10 + 9 * ((-chart.coordinate) % 10)
    assert _literal_children(_value(chart, 5)) == ()


@pytest.mark.parametrize(
    ("chart", "expected_value", "expected_headroom"),
    [
        (BoundaryChart("near", 1, 0, 9), 200_003, 99_997),
        (BoundaryChart("near", 9, 0, 3), 1_000_068, 999_932),
    ],
)
def test_sector_crossing_rebases_headroom_before_tropical_composition(
    chart: BoundaryChart, expected_value: int, expected_headroom: int
) -> None:
    # Endpoint differences summarize Near runs only within one fixed chart.
    # Adding them across a seam without the new boundary would reject these
    # legal edges: old headroom minus the increment is negative in both cases.
    source = _value(chart, 5)
    assert _literal_children(source) == (expected_value,)
    move = chart_step(5, chart)
    target = move.next_chart
    assert target is not None and target.kind == "entry"
    assert move.weight == boundary_chart.UNIT_WEIGHT
    assert _value(target, 5) == expected_value
    assert target.delta == chart.delta + int(chart.leading == 9)
    untransported = chart.coordinate - move.literal_increment
    assert untransported < 0
    receiving_scale = 10 ** (5 + target.delta)
    assert untransported + receiving_scale == expected_headroom
    assert receiving_scale - target.coordinate == expected_headroom


def test_positive_headroom_does_not_prove_unique_continuation() -> None:
    # Tropical nonnegativity alone does not exclude an equality/fork seam.
    chart = BoundaryChart("near", 1, 0, 82)
    value = _value(chart, 5)
    children = _literal_children(value)
    assert children == (199_999, 200_000)
    assert chart.coordinate > 0
    assert chart.coordinate - (children[0] - value) == 1
    assert chart.coordinate - (children[1] - value) == 0
    move = chart_step(5, chart)
    assert move.next_chart is None and move.fork_a == 2
    assert move.terminal_chart == chart
    assert move.weight == boundary_chart.ZERO_WEIGHT


@pytest.mark.parametrize("component", ["chart", "weight"])
def test_macro_rejects_changed_terminal_evidence(
    monkeypatch: pytest.MonkeyPatch, component: str
) -> None:
    original = boundary_chart.chart_step

    def altered(
        residue: int,
        chart: BoundaryChart,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> boundary_chart.ChartMove:
        assert charge_bits is None
        move = original(residue, chart)
        if move.next_chart is not None:
            return move
        if component == "chart":
            return replace(
                move, terminal_chart=replace(chart, coordinate=chart.coordinate + 1)
            )
        return replace(move, weight=boundary_chart.UNIT_WEIGHT)

    monkeypatch.setattr(boundary_chart, "chart_step", altered)
    with pytest.raises(AssertionError, match="terminal move"):
        construct_macro(BoundaryState("N", 2, 10))


@pytest.mark.parametrize("forged_a", [None, 3])
def test_macro_rejects_forged_fork_children(
    monkeypatch: pytest.MonkeyPatch, forged_a: int | None
) -> None:
    original = boundary_chart.chart_step

    def altered(
        residue: int,
        chart: BoundaryChart,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> boundary_chart.ChartMove:
        move = original(residue, chart, charge_bits=charge_bits)
        return replace(move, fork_a=forged_a) if move.fork_a is not None else move

    monkeypatch.setattr(boundary_chart, "chart_step", altered)
    with pytest.raises(AssertionError, match="terminal alternatives"):
        construct_macro(BoundaryState("N", 2, 10))


def test_macro_rejects_spurious_fork_at_landmine(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = boundary_chart.chart_step

    def altered(
        residue: int,
        chart: BoundaryChart,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> boundary_chart.ChartMove:
        move = original(residue, chart, charge_bits=charge_bits)
        return (
            replace(move, fork_a=2)
            if move.next_chart is None and move.fork_a is None
            else move
        )

    monkeypatch.setattr(boundary_chart, "chart_step", altered)
    with pytest.raises(AssertionError, match="terminal alternatives"):
        construct_macro(BoundaryState("N", 3, 5))


def test_exhaustion_never_publishes_a_landmine(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(boundary_chart, "MAX_CHART_MOVES", 1)
    with pytest.raises(ValueError, match="finite seam bound"):
        construct_macro(BoundaryState("N", 2, 10))


@pytest.mark.parametrize(
    "chart",
    [
        BoundaryChart("entry", 2, 0, 99),
        BoundaryChart("near", 2, 0, 0),
        BoundaryChart("near", 0, 0, 1),
        BoundaryChart("near", 9, 0, 541),
        BoundaryChart("entry", 2, -1, 0),
    ],
)
def test_invalid_chart_fails_before_any_modular_power(
    monkeypatch: pytest.MonkeyPatch, chart: BoundaryChart
) -> None:
    def forbidden(*_args: int) -> int:
        raise AssertionError("invalid chart performed modular construction")

    monkeypatch.setattr(arithmetic, "pow", forbidden, raising=False)
    with pytest.raises(ValueError, match="invalid comma boundary chart"):
        chart_step(10, chart)


def test_small_power_periods_cover_every_cycle_and_exponent_residue() -> None:
    displacements = {
        arithmetic.cycle_transfer(f, d).displacement
        for f in range(1, 10)
        for d in range(10)
    }
    assert len(displacements) == 17
    for displacement in displacements:
        for residue in range(924):
            representative = residue if residue >= 5 else residue + 924
            actual = arithmetic.cycle_power_residue(displacement, residue)
            for exponent in (
                representative,
                representative + 924,
                representative + 1848,
            ):
                assert actual == pow(10, exponent, displacement)


def test_entry_uses_only_small_modular_powers(monkeypatch: pytest.MonkeyPatch) -> None:
    exponents: list[int] = []

    def bounded(base: int, exponent: int, modulus: int) -> int:
        assert base == 10 and 5 <= exponent <= 32 and 0 < modulus <= 540
        exponents.append(exponent)
        return pow(base, exponent, modulus)

    monkeypatch.setattr(arithmetic, "pow", bounded, raising=False)
    for residue in (0, 4, 5, 10, 923):
        construct_macro(BoundaryState("N", 2, residue))
    assert exponents


@pytest.mark.parametrize(
    "displacement,residue", [(0, 0), (541, 10), (60, -1), (60, 924)]
)
def test_small_power_residue_rejects_unadmitted_inputs(
    monkeypatch: pytest.MonkeyPatch, displacement: int, residue: int
) -> None:
    def forbidden(*_args: int) -> int:
        raise AssertionError("invalid residue performed arithmetic")

    monkeypatch.setattr(arithmetic, "pow", forbidden, raising=False)
    with pytest.raises(ValueError, match="comma"):
        arithmetic.cycle_power_residue(displacement, residue)
