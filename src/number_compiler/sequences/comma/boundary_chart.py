"""Canonical weighted Entry/Near constructor for comma boundary macros.

This is the executable counterpart of ``comma_weighted_step``. Finite-graph
tooling erases weights from these moves; it has no second constructor. No representative
decimal endpoint is evaluated to choose a move. Global branch safety still
requires a checked lifting and winning-cycle instance.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from dataclasses import dataclass
from typing import Literal

from number_compiler.sequences.comma.arithmetic import (
    CycleTransfer,
    _sector_child_increments,
    classify_near_port,
    cycle_power_residue,
    cycle_transfer,
)

PERIOD = 924
MAX_CHART_MOVES = 4096


@dataclass(frozen=True, slots=True)
class BoundaryChart:
    kind: Literal["entry", "near"]
    leading: int
    delta: int
    coordinate: int


@dataclass(frozen=True, slots=True)
class ChartWeight:
    """Exact ``(scale * 10**(p + exponent_delta) + offset) / denominator``.

    The exponent remains symbolic while the finite control is constructed.
    Integrality and admission concern the receiving exponent, not a sampled
    representative value.
    """

    scale: int
    exponent_delta: int
    offset: int
    denominator: int


ZERO_WEIGHT = ChartWeight(0, 0, 0, 1)
UNIT_WEIGHT = ChartWeight(0, 0, 1, 1)


@dataclass(frozen=True, slots=True)
class ChartMove:
    next_chart: BoundaryChart | None
    weight: ChartWeight
    fork_a: int | None = None
    cycle: CycleTransfer | None = None
    terminal_chart: BoundaryChart | None = None
    literal_increment: int = 0


def initial_chart(kind: Literal["N", "Z"], a: int) -> BoundaryChart:
    if kind not in ("N", "Z") or type(a) is not int or not 2 <= a <= 9:
        raise ValueError("invalid comma boundary constructor")
    return (
        BoundaryChart("near", a - 1, 0, 1)
        if kind == "N"
        else BoundaryChart("entry", a, 0, 0)
    )


def _validate_chart(residue: int, chart: BoundaryChart) -> None:
    if (
        type(residue) is not int
        or not 0 <= residue < PERIOD
        or chart.kind not in ("entry", "near")
        or any(
            type(v) is not int for v in (chart.leading, chart.delta, chart.coordinate)
        )
        or not 1 <= chart.leading <= 9
        or chart.delta < 0
        or chart.coordinate < 0
        or (chart.kind == "entry" and chart.coordinate > 98)
        or (chart.kind == "near" and not 1 <= chart.coordinate <= 540)
    ):
        raise ValueError("invalid comma boundary chart")


def chart_step(
    residue: int,
    chart: BoundaryChart,
    *,
    charge_bits: Callable[[int], None] | None = None,
) -> ChartMove:
    """One chart move; an Entry jump retains its exact cycle descriptor.

    A Near move consumes one literal edge, except at a fork/landmine where
    it consumes zero. Entry cycle weights are evaluated at the receiving
    exponent, not at the residue's representative exponent.
    """
    _validate_chart(residue, chart)
    f, delta, x = chart.leading, chart.delta, chart.coordinate
    if charge_bits is not None:
        charge_bits(residue.bit_length() + delta.bit_length() + x.bit_length() + 16)
    if chart.kind == "entry":
        transfer = cycle_transfer(f, x % 10)
        phase = (residue + delta) % PERIOD
        power = cycle_power_residue(
            transfer.displacement, phase, charge_bits=charge_bits
        )
        extra = int(f < 9)
        headroom = 1 + extra + (power - x - 1 - extra) % transfer.displacement
        if charge_bits is not None:
            charge_bits(
                transfer.period.bit_length() + x.bit_length() + headroom.bit_length()
            )
        return ChartMove(
            BoundaryChart("near", f, delta, headroom),
            ChartWeight(
                transfer.period,
                delta,
                -transfer.period * (x + headroom),
                transfer.displacement,
            ),
            cycle=transfer,
        )

    digit = (-x) % 10
    increments = _sector_child_increments(f, digit, x)
    if not increments:
        return ChartMove(None, ZERO_WEIGHT, terminal_chart=chart)
    if len(increments) == 2:
        return ChartMove(None, ZERO_WEIGHT, fork_a=f + 1, terminal_chart=chart)
    increment = increments[0]
    if x > increment:
        return ChartMove(
            BoundaryChart("near", f, delta, x - increment),
            UNIT_WEIGHT,
            literal_increment=increment,
        )
    return ChartMove(
        BoundaryChart(
            "entry", f + 1 if f < 9 else 1, delta + int(f == 9), increment - x
        ),
        UNIT_WEIGHT,
        literal_increment=increment,
    )


def chart_moves(
    kind: Literal["N", "Z"],
    a: int,
    residue: int,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> Iterator[tuple[BoundaryChart, ChartMove]]:
    """Construct a bounded macro, retaining its terminal chart.

    Exhaustion is a failure, never a landmine or a branch-safety verdict.
    Grouped construction uses the weighted port only for strict interior
    Near prefixes. Its weight is physical phase time, never diagonal dwell.
    """
    if type(grouped_near) is not bool:
        raise ValueError("comma chart grouping requires a Boolean selector")
    chart = initial_chart(kind, a)
    for _ in range(MAX_CHART_MOVES):
        if charge is not None:
            charge(1)
        _validate_chart(residue, chart)
        if (
            grouped_near
            and chart.kind == "near"
            and chart.coordinate
            > 10 * ((-chart.coordinate) % 10) + chart.leading + int(chart.leading < 9)
        ):
            prefix = classify_near_port(
                chart.leading,
                chart.coordinate,
                charge_work=charge,
                charge_bits=charge_bits,
            )
            if prefix.physical_steps <= 0:
                raise ArithmeticError(
                    "comma interior Near prefix has zero physical time"
                )
            move = ChartMove(
                BoundaryChart(
                    "near", chart.leading, chart.delta, prefix.terminal_headroom
                ),
                ChartWeight(0, 0, prefix.physical_steps, 1),
                literal_increment=chart.coordinate - prefix.terminal_headroom,
            )
        else:
            move = chart_step(residue, chart, charge_bits=charge_bits)
        yield chart, move
        if move.next_chart is None:
            return
        chart = move.next_chart
    raise ValueError("comma boundary macro exceeded its finite seam bound")
