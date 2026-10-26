from __future__ import annotations

import builtins
from typing import cast

import pytest

from number_compiler.sequences.comma.boundary_carry_clock import (
    GuardedC1ChartPower,
    SymbolicEntryCarryClock,
    powered_chart_carry,
    symbolic_entry_carry_clock,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    ChartWeight,
    chart_step,
)


def _duration_at_exponent(weight: ChartWeight, exponent: int) -> int:
    numerator: int = (
        weight.scale * int(10 ** (exponent + weight.exponent_delta)) + weight.offset
    )
    result: int = numerator // weight.denominator
    remainder: int = numerator % weight.denominator
    assert remainder == 0
    return result


def _literal_carry_out(value: int, increment: int, wire: int) -> bool:
    carry = 0
    for column in range(wire + 1):
        carry = (
            value // (10**column) % 10 + increment // (10**column) % 10 + carry
        ) // 10
    return bool(carry)


@pytest.mark.parametrize(
    ("chart", "fork_a"),
    (
        (BoundaryChart("near", 2, 0, 73), 3),
        (BoundaryChart("near", 9, 0, 19), None),
    ),
)
def test_powered_chart_rejects_first_terminal_fork_or_landmine(
    chart: BoundaryChart, fork_a: int | None
) -> None:
    move = chart_step(5, chart)
    assert move.next_chart is None
    assert move.fork_a == fork_a

    with pytest.raises(ValueError):
        powered_chart_carry(5, chart, 5, 1)


def test_symbolic_entry_clock_keeps_large_width_symbolic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    exponent = 5 + 924 * 1_000_000
    exponent_phase = exponent % PERIOD
    chart = BoundaryChart("entry", 2, 0, 0)
    original_pow = builtins.pow

    def reject_decimal_materialization(
        base: int, power: int, modulus: int | None = None
    ) -> int:
        if base == 10 and power > 1_000 and modulus is None:
            pytest.fail("symbolic entry clock materialized its decimal width")
        if modulus is None:
            return int(original_pow(base, power))
        return int(original_pow(base, power, modulus))

    monkeypatch.setattr(builtins, "pow", reject_decimal_materialization)
    clock = symbolic_entry_carry_clock(exponent_phase, chart, exponent)

    assert clock.width == exponent
    assert clock.selected_exponent_phase == exponent_phase
    assert clock.duration.scale > 0
    assert clock.duration.exponent_delta == chart.delta
    assert clock.duration.offset.bit_length() < 128
    assert clock.wire_formula(1).shift == chart.delta - 2
    assert clock.wire_formula(2).shift == chart.delta - 3


def test_entry_higher_and_top_wire_totals_match_literal_addition() -> None:
    exponent = 5
    exponent_phase = exponent % 924
    chart = BoundaryChart("entry", 2, 0, 0)
    clock = symbolic_entry_carry_clock(exponent_phase, chart, exponent)
    steps = _duration_at_exponent(clock.duration, exponent)
    powered = powered_chart_carry(exponent_phase, chart, exponent, steps)

    current = chart.leading * 10**exponent + chart.coordinate
    literal_totals = [0] * (powered.width + 2)
    for _ in range(steps):
        increment = 10 * (current % 10) + chart.leading
        for wire in range(len(literal_totals)):
            literal_totals[wire] += int(_literal_carry_out(current, increment, wire))
        current += increment

    for wire, expected in enumerate(literal_totals):
        assert powered.wire_total(wire) == expected


def test_closed_entry_c1_count_matches_the_guarded_powered_oracle() -> None:
    exponent = 5
    exponent_phase = exponent % 924
    chart = BoundaryChart("entry", 2, 0, 0)
    clock = symbolic_entry_carry_clock(exponent_phase, chart, exponent)
    steps = _duration_at_exponent(clock.duration, exponent)
    powered = powered_chart_carry(exponent_phase, chart, exponent, steps)
    headroom = clock.destination.coordinate
    expected_count = 10 ** (exponent - 2) - (headroom + 99) // 100
    formula = clock.wire_formula(1)

    assert clock.target_suffix == (-headroom) % 100
    assert powered.carry_count == expected_count
    assert not formula.is_zero
    assert 10 ** (exponent + formula.shift) - formula.subtract == expected_count


def test_chart_power_rejects_wrong_phase_boolean_duration_and_mutated_phase() -> None:
    chart = BoundaryChart("entry", 2, 0, 0)
    with pytest.raises(ValueError, match="clock"):
        powered_chart_carry(6, chart, 5, 1)
    with pytest.raises(ValueError, match="nonnegative duration"):
        powered_chart_carry(5, chart, 5, True)
    with pytest.raises(ValueError, match="invalid comma exponent clock"):
        powered_chart_carry(cast(int, True), chart, 5, 1)

    forged_chart = BoundaryChart("entry", 2, 0, 0)
    object.__setattr__(forged_chart, "coordinate", -1)
    with pytest.raises(ValueError, match="invalid comma boundary chart"):
        powered_chart_carry(5, forged_chart, 5, 1)

    powered = powered_chart_carry(5, chart, 5, 1)
    object.__setattr__(powered.action, "_count", powered.action.count + 1)
    with pytest.raises(ValueError, match="snapshot"):
        powered.wire_total(1)


def test_guarded_clock_records_are_factory_issued_and_snapshot_checked() -> None:
    chart = BoundaryChart("entry", 2, 0, 0)
    with pytest.raises(TypeError, match="issued by"):
        GuardedC1ChartPower()
    with pytest.raises(TypeError, match="issued by"):
        SymbolicEntryCarryClock()

    exponent = 5
    clock = symbolic_entry_carry_clock(exponent % 924, chart, exponent)
    object.__setattr__(clock, "_duration", ChartWeight(1, 0, 0, 1))
    with pytest.raises(ValueError, match="snapshot"):
        clock.wire_formula(1)

    powered = powered_chart_carry(exponent % 924, chart, exponent, 1)
    original_headroom = powered.headroom_weight
    object.__setattr__(
        powered,
        "_headroom_weight",
        ChartWeight(
            original_headroom.scale,
            original_headroom.exponent_delta,
            original_headroom.offset,
            original_headroom.denominator,
        ),
    )
    with pytest.raises(ValueError, match="snapshot"):
        powered.wire_total(1)


def test_entry_duration_guard_does_not_charge_an_unmaterialized_width() -> None:
    exponent = 5 + 924 * 1_000_000
    charges: list[int] = []
    powered = powered_chart_carry(
        exponent % 924,
        BoundaryChart("entry", 2, 0, 0),
        exponent,
        1,
        charge_bits=charges.append,
    )

    assert powered.duration == 1
    assert charges
    assert max(charges) < 1_024


@pytest.mark.parametrize("charge_name", ("work", "bits"))
def test_powered_chart_propagates_budget_callback_failure(charge_name: str) -> None:
    class BudgetExceeded(RuntimeError):
        pass

    def fail(_amount: int) -> None:
        raise BudgetExceeded(charge_name)

    with pytest.raises(BudgetExceeded, match=charge_name):
        if charge_name == "work":
            powered_chart_carry(
                5, BoundaryChart("entry", 2, 0, 0), 5, 1, charge_work=fail
            )
        else:
            powered_chart_carry(
                5, BoundaryChart("entry", 2, 0, 0), 5, 1, charge_bits=fail
            )
