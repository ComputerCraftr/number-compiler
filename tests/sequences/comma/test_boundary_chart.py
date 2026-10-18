"""Chart/control regressions independent of finite rank data."""

from __future__ import annotations

from collections.abc import Callable, Iterator
from dataclasses import replace
from math import gcd
from typing import Literal, cast

import pytest

from number_compiler.sequences.comma import (
    arithmetic,
    boundary_chart,
    boundary_return,
)
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
from number_compiler.sequences.comma.domain import (
    canonical_entry_coordinate,
    coarse_entry_coordinate,
    decade_root_coordinate,
)
from tests.support.comma_oracles import literal_children as _literal_children


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
    assert chart is not None
    assert chart == BoundaryChart("near", a - 1, 0, 1)
    move = chart_step(10, chart)
    assert move.next_chart is not None
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


@pytest.mark.parametrize("kind", ["N", "Z"])
@pytest.mark.parametrize("a,residue", [(2, 10), (3, 5), (9, 923)])
def test_grouped_near_moves_refine_the_single_edge_reference(
    kind: Literal["N", "Z"], a: int, residue: int
) -> None:
    reference = iter(chart_moves(kind, a, residue))
    for chart, move in chart_moves(kind, a, residue, grouped_near=True):
        source, first = next(reference)
        assert source == chart
        if move == first:
            continue
        assert chart.kind == "near" and move.cycle is None
        assert move.next_chart is not None and move.next_chart.kind == "near"
        assert move.weight.scale == 0 and move.weight.denominator == 1
        increment = 0
        current, edge = source, first
        for index in range(move.weight.offset):
            assert edge.weight == boundary_chart.UNIT_WEIGHT
            assert edge.next_chart is not None and edge.next_chart.kind == "near"
            assert edge.next_chart.leading == chart.leading
            increment += edge.literal_increment
            current = edge.next_chart
            if index + 1 < move.weight.offset:
                next_source, edge = next(reference)
                assert next_source == current
        assert current == move.next_chart
        assert increment == move.literal_increment
        assert current.coordinate > int(chart.leading < 9)
    assert next(reference, None) is None


@pytest.mark.parametrize("kind", ["N", "Z"])
@pytest.mark.parametrize("a,residue", [(2, 10), (3, 5), (9, 923)])
def test_grouped_macro_is_the_same_complete_weighted_return(
    monkeypatch: pytest.MonkeyPatch,
    kind: Literal["N", "Z"],
    a: int,
    residue: int,
) -> None:
    source = BoundaryState(kind, a, residue)
    grouped = construct_macro(source, grouped_near=True)
    original = chart_moves

    def scalar(
        kind: Literal["N", "Z"],
        a: int,
        residue: int,
        *,
        charge: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
        grouped_near: bool = False,
    ) -> Iterator[tuple[BoundaryChart, boundary_chart.ChartMove]]:
        assert grouped_near
        return original(kind, a, residue, charge=charge, charge_bits=charge_bits)

    monkeypatch.setattr(boundary_return, "chart_moves", scalar)
    reference = construct_macro(source, grouped_near=True)
    assert grouped == reference


def test_grouped_constructor_never_replays_strict_near_edges(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    reference = tuple(chart_moves("N", 2, 10))
    grouped = tuple(chart_moves("N", 2, 10, grouped_near=True))
    assert len(grouped) < len(reference) == 93
    original = boundary_chart.chart_step
    calls = 0

    def seam_only(
        residue: int,
        chart: BoundaryChart,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> boundary_chart.ChartMove:
        nonlocal calls
        assert not (
            chart.kind == "near"
            and chart.coordinate
            > 10 * ((-chart.coordinate) % 10) + chart.leading + int(chart.leading < 9)
        ), "grouped construction replayed a strict-interior Near edge"
        calls += 1
        return original(residue, chart, charge_bits=charge_bits)

    monkeypatch.setattr(boundary_chart, "chart_step", seam_only)
    charges: list[int] = []
    macro = construct_macro(
        BoundaryState("N", 2, 10), charge=charges.append, grouped_near=True
    )
    assert macro.ordered_children
    assert 0 < calls < len(grouped) < len(reference)
    assert sum(charges) > len(grouped)  # Port construction is charged too.


def test_default_macro_avoids_the_more_expensive_grouped_classifier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = BoundaryState("N", 2, 10)
    grouped_work: list[int] = []
    grouped = construct_macro(source, grouped_near=True, charge=grouped_work.append)

    def forbidden(*_args: object, **_kwargs: object) -> arithmetic.NearPortReturn:
        raise AssertionError("default macro constructed a grouped port catalog")

    monkeypatch.setattr(boundary_chart, "classify_near_port", forbidden)
    default_work: list[int] = []
    default = construct_macro(source, charge=default_work.append)
    assert default == grouped
    assert 0 < sum(default_work) < sum(grouped_work)


def test_grouped_macro_rejects_a_consistent_but_unsafe_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = arithmetic.classify_near_port

    def forged(
        leading: int,
        headroom: int,
        *,
        charge_work: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> arithmetic.NearPortReturn:
        result = original(
            leading, headroom, charge_work=charge_work, charge_bits=charge_bits
        )
        digit = (-headroom) % 10
        for steps in range(result.physical_steps + 1, result.physical_steps + 11):
            terminal = headroom - arithmetic.phase_prefix_displacement(
                leading, digit, steps
            )
            if terminal == 1 and leading < 9:
                return replace(result, physical_steps=steps, terminal_headroom=terminal)
        return result

    # H82 at f1 is a fork; its lower child has H1. A forged grouped move
    # can match the phase displacement exactly while silently skipping it.
    monkeypatch.setattr(
        boundary_chart,
        "initial_chart",
        lambda _kind, _a: BoundaryChart("near", 1, 0, 153),
    )
    monkeypatch.setattr(boundary_chart, "classify_near_port", forged)
    with pytest.raises(AssertionError, match="phase semantics"):
        construct_macro(BoundaryState("N", 2, 10), grouped_near=True)


def test_grouped_selector_requires_an_exact_boolean() -> None:
    with pytest.raises(ValueError, match="Boolean selector"):
        tuple(chart_moves("N", 2, 10, grouped_near=cast(bool, 1)))


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


@pytest.mark.parametrize(
    ("leading", "coordinate", "expected"),
    [
        (1, 90, True),
        (1, 91, False),
        (1, 98, False),
        (2, 91, True),
        (2, 92, False),
        (9, 98, True),
        (9, 99, False),
    ],
)
def test_canonical_entry_domain_is_sector_specific(
    leading: int, coordinate: int, expected: bool
) -> None:
    assert canonical_entry_coordinate(leading, coordinate) is expected


def test_coarse_and_canonical_entry_domains_remain_distinct() -> None:
    assert coarse_entry_coordinate(1, 98)
    assert not canonical_entry_coordinate(1, 98)
    assert (
        sum(coarse_entry_coordinate(f, x) for f in range(1, 10) for x in range(99))
        == 891
    )
    assert (
        sum(canonical_entry_coordinate(f, x) for f in range(1, 10) for x in range(99))
        == 855
    )


def test_fabricated_sector_one_entry_is_rejected_before_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    assert decade_root_coordinate(1, 90)
    assert not decade_root_coordinate(1, 91)

    def forbidden(*_args: int) -> object:
        raise AssertionError("invalid chart performed cycle construction")

    monkeypatch.setattr(boundary_chart, "entry_headroom", forbidden)
    with pytest.raises(ValueError, match="invalid comma boundary chart"):
        chart_step(10, BoundaryChart("entry", 1, 0, 98))


@pytest.mark.parametrize("leading", range(1, 10))
def test_runtime_chart_step_uses_each_sector_canonical_limit(leading: int) -> None:
    limit = 89 + leading
    move = chart_step(10, BoundaryChart("entry", leading, 0, limit))
    assert move.next_chart is not None
    with pytest.raises(ValueError, match="invalid comma boundary chart"):
        chart_step(10, BoundaryChart("entry", leading, 0, limit + 1))


@pytest.mark.parametrize("leading", range(1, 10))
def test_near_one_crossing_targets_the_canonical_entry_boundary(leading: int) -> None:
    source = BoundaryChart("near", leading, 0, 1)
    move = chart_step(10, source)
    assert move.next_chart == (
        BoundaryChart("entry", leading + 1, 0, 90 + leading)
        if leading < 9
        else BoundaryChart("entry", 1, 1, 90)
    )
    assert move.next_chart is not None
    assert _literal_children(_value(source, 10)) == (_value(move.next_chart, 10),)


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


@pytest.mark.parametrize("exponent", (3, 4))
def test_chart_scale_alone_does_not_admit_periodic_phase_transport(
    exponent: int,
) -> None:
    displacement = arithmetic.cycle_transfer(3, 0).displacement
    assert displacement == 480
    assert 10**exponent > 98 and 10**exponent >= 540
    assert pow(10, exponent, displacement) != pow(10, exponent + 924, displacement)
    assert pow(10, 5, displacement) == pow(10, 5 + 924, displacement)


def test_entry_uses_recursive_cores_without_modular_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    inverse_moduli: list[int] = []

    def bounded(base: int, exponent: int, modulus: int) -> int:
        if exponent == -1:
            assert 1 <= base <= 9 and modulus in (2, 5, 10)
            assert gcd(base, modulus) == 1
            inverse_moduli.append(modulus)
        else:
            pytest.fail("Entry rebuilt a decimal modular power")
        return pow(base, exponent, modulus)

    monkeypatch.setattr(arithmetic, "pow", bounded, raising=False)
    for residue in (0, 4, 5, 10, 923):
        construct_macro(BoundaryState("N", 2, residue))
        construct_macro(BoundaryState("N", 2, residue), grouped_near=True)
    assert not inverse_moduli


@pytest.mark.parametrize("core", (1, 3, 7, 11, 13, 21, 23, 27, 29))
def test_recursive_core_matches_modular_power_at_all_phases(core: int) -> None:
    for exponent in (*range(924), 10**100 + 29):
        assert arithmetic.recursive_core_residue(core, exponent) == pow(
            10, exponent, core
        )


@pytest.mark.parametrize("core,exponent", ((True, 0), (5, 0), (7, True), (7, -1)))
def test_recursive_core_rejects_unadmitted_arguments(core: int, exponent: int) -> None:
    with pytest.raises(ValueError, match="recursive core"):
        arithmetic.recursive_core_residue(core, exponent)


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
