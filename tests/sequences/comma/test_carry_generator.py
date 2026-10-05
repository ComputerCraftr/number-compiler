from __future__ import annotations

from dataclasses import fields

import pytest

from number_compiler.sequences.comma import carry_generator as generator
from number_compiler.sequences.comma.arithmetic import comma_children
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    near_chart_target,
)
from number_compiler.sequences.comma.carry_generator import (
    BoundC1Return,
    C1Phase,
    C1Return,
    apply_high_prefix_cylinder,
    carry_wire,
    high_prefix_cylinder,
    source_bound_return,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.decisive_endpoint import (
    DecisiveEndpoint,
    source_endpoint,
)


def _literal_step(sector: int, suffix: int) -> tuple[int, bool, bool, int]:
    ones = suffix % 10
    increment = 10 * ones + sector
    total = suffix + increment
    next_suffix = total % 100
    c0 = (ones + sector) >= 10
    c1 = total >= 100
    return next_suffix, c0, c1, increment


def _periodic_oracle(sector: int, suffix: int, steps: int) -> tuple[int, int]:
    """Independent cycle detection followed by quotient/remainder counting."""
    seen: dict[int, int] = {}
    states: list[int] = []
    outputs: list[int] = []
    current = suffix
    while current not in seen:
        seen[current] = len(states)
        states.append(current)
        following, _, c1, _ = _literal_step(sector, current)
        outputs.append(int(c1))
        current = following
    cycle_start = seen[current]
    cycle_size = len(states) - cycle_start
    if steps < len(states):
        target = states[steps]
        count = sum(outputs[:steps])
        return target, count
    prefix_count = sum(outputs[:cycle_start])
    cycle_count = sum(outputs[cycle_start:])
    remaining = steps - cycle_start
    complete, tail = divmod(remaining, cycle_size)
    target = states[cycle_start + tail]
    count = (
        prefix_count
        + complete * cycle_count
        + sum(outputs[cycle_start : cycle_start + tail])
    )
    return target, count


def _literal_addition_carry(value: int, increment: int, wire: int) -> bool:
    """Propagate a decimal addition column by column as an independent oracle."""
    carry = 0
    for column in range(wire + 1):
        value_digit = value // (10**column) % 10
        increment_digit = increment // (10**column) % 10
        carry = (value_digit + increment_digit + carry) // 10
    return bool(carry)


def test_phase_stores_only_immutable_crt_coordinates() -> None:
    assert tuple(field.name for field in fields(C1Phase)) == (
        "sector",
        "mod4",
        "mod25",
    )
    for sector in range(1, 10):
        for suffix in range(100):
            phase = C1Phase.from_suffix(sector, suffix)
            assert phase.suffix == suffix
            for field in fields(phase):
                with pytest.raises((AttributeError, TypeError)):
                    setattr(phase, field.name, 0)


def test_forged_phase_coordinates_are_rejected_at_observation() -> None:
    phase = C1Phase.from_suffix(3, 17)
    object.__setattr__(phase, "mod25", 25)
    with pytest.raises(ValueError, match="forged comma c1 phase"):
        _ = phase.suffix
    with pytest.raises(ValueError, match="forged comma c1 phase"):
        phase.step()


def test_c1_phase_alias_requires_decisive_endpoint_admission() -> None:
    """A low C1 phase alone aliases two broad Near charts with different moves.

    The first chart is also a source-selected decisive endpoint. The second is
    admitted by the broad Near chart owner but is outside the decisive endpoint
    domain, so this is not evidence of a collision on source-selected roots.
    """
    source_endpoint_82 = source_endpoint(CyclotomicClock.from_phase(14), 10)
    assert source_endpoint_82.endpoint == DecisiveEndpoint(1, 82)

    phase_82 = C1Phase.from_suffix(1, 82)
    phase_182 = C1Phase.from_suffix(1, 182 % 100)
    assert phase_82 == phase_182
    assert C1Return(phase_82, 7) == C1Return(phase_182, 7)

    move_82 = near_chart_target(BoundaryChart("near", 1, 0, 82))
    move_182 = near_chart_target(BoundaryChart("near", 1, 0, 182))
    assert move_82.fork_a == 2
    assert move_82.next_chart is None
    assert move_182.fork_a is None
    assert move_182.next_chart == BoundaryChart("near", 1, 0, 101)

    with pytest.raises(ValueError, match="outside the decisive Near boundary"):
        DecisiveEndpoint(1, 182)


def test_all_900_phases_and_durations_zero_through_fifty() -> None:
    for sector in range(1, 10):
        for suffix in range(100):
            phase = C1Phase.from_suffix(sector, suffix)
            literal_suffix = suffix
            literal_count = 0
            for steps in range(51):
                result = C1Return(phase, steps)
                assert result.target.suffix == literal_suffix
                assert result.target.sector == sector
                assert result.count == literal_count
                _, c0, c1, _ = _literal_step(sector, literal_suffix)
                assert phase.advance(steps).c0 == c0
                assert phase.advance(steps).c1 == c1
                if steps < 50:
                    next_suffix, _, _, _ = _literal_step(sector, literal_suffix)
                    assert phase.advance(steps + 1).suffix == next_suffix
                    literal_suffix = next_suffix
                    literal_count += int(c1)


@pytest.mark.parametrize(
    "sector,suffix",
    ((1, 0), (2, 54), (4, 99), (5, 54), (5, 45), (8, 73), (9, 99)),
)
def test_large_durations_match_independent_periodic_oracle(
    sector: int, suffix: int
) -> None:
    phase = C1Phase.from_suffix(sector, suffix)
    for steps in (2**130 + 17, 10**45 + 49, 10**60 + 2**80 + 3):
        expected_suffix, expected_count = _periodic_oracle(sector, suffix, steps)
        result = C1Return(phase, steps)
        assert (result.target.suffix, result.count) == (
            expected_suffix,
            expected_count,
        )
        assert result.target == phase.advance(steps)
        assert result.target == phase.advance(steps % 50)


@pytest.mark.parametrize("suffix", (54, 45))
def test_sector_five_puncture_and_chronological_composition(suffix: int) -> None:
    phase = C1Phase.from_suffix(5, suffix)
    source = 5 * 10**12 + suffix
    whole = source_bound_return(source, phase, 17)
    first = source_bound_return(source, phase, 6)
    middle_value = source + first.action.displacement()
    second = source_bound_return(middle_value, first.target, 11)
    assert type(whole) is BoundC1Return
    joined = first.then(second)
    assert joined == whole
    assert joined.action.count == first.count + second.count
    assert joined.target_high == whole.target_high


def test_composed_returns_do_not_rebuild_cycle_displacement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    phase = C1Phase.from_suffix(3, 28)
    first = C1Return(phase, 123456789)
    second = C1Return(first.target, 987654321)
    direct = C1Return(phase, first.steps + second.steps)

    def forbidden(*_args: object, **_kwargs: object) -> int:
        pytest.fail("return composition re-entered the displacement owner")

    monkeypatch.setattr(generator, "phase_prefix_displacement", forbidden)
    joined = first.then(second)
    assert (joined.start, joined.target, joined.steps, joined.count) == (
        direct.start,
        direct.target,
        direct.steps,
        direct.count,
    )


def test_forged_return_counters_are_rejected_without_repowering() -> None:
    phase = C1Phase.from_suffix(4, 62)
    result = C1Return(phase, 0)
    following = C1Return(result.target, 3)
    object.__setattr__(result, "_count", 99)
    with pytest.raises(ValueError, match="snapshot"):
        _ = result.count
    with pytest.raises(ValueError, match="snapshot"):
        result.then(following)


def test_forged_bound_prefix_and_inner_action_are_rejected() -> None:
    phase = C1Phase.from_suffix(5, 45)
    source = 5 * 10**12 + 45
    result = source_bound_return(source, phase, 4)
    object.__setattr__(result, "_target_high", result.target_high + 1)
    with pytest.raises(ValueError, match="snapshot"):
        result.high_cylinder(2)

    result = source_bound_return(source, phase, 4)
    object.__setattr__(result.action, "_count", result.count + 1)
    with pytest.raises(ValueError, match="snapshot"):
        result.carry_wire(4)


def test_completed_bound_factory_checks_high_prefix_cocycle() -> None:
    action = C1Return(C1Phase.from_suffix(5, 45), 4)
    with pytest.raises(ValueError, match="disagrees with its count"):
        generator._completed_bound_return(
            10**20,
            action,
            10**20 + action.count + 1,
        )


def test_source_bound_return_rejects_mismatches_and_sector_crossing() -> None:
    phase = C1Phase.from_suffix(5, 54)
    with pytest.raises(ValueError, match="does not match"):
        source_bound_return(5 * 10**8 + 55, phase, 1)
    with pytest.raises(ValueError, match="three decimal digits"):
        source_bound_return(54, phase, 1)

    source = 5 * 10**4 + 54
    with pytest.raises(ValueError, match="crosses"):
        source_bound_return(source, phase, 10**8)

    # The guard is a sufficient interior admission test. At this fork both
    # physical children exist, so the fixed-sector low child is intentionally
    # outside that guard's claim.
    with pytest.raises(ValueError, match="crosses"):
        source_bound_return(118, C1Phase.from_suffix(1, 18), 1)
    assert comma_children(118) == (199, 200)


def test_completed_return_checks_target_without_recounting() -> None:
    phase = C1Phase.from_suffix(4, 62)
    with pytest.raises(ValueError, match="target disagrees"):
        generator._completed_return(phase, phase.step(), 0, 0)


def test_high_prefix_cylinders_are_exact_and_projective() -> None:
    for high in (0, 1, 999, 10**40 + 123456789):
        for count in (0, 1, 27, 10**25 + 3):
            for precision in range(21):
                expected = (high + count) % (10**precision)
                assert apply_high_prefix_cylinder(high, count, precision) == expected
            for precision in range(20):
                low = apply_high_prefix_cylinder(high, count, precision)
                high_precision = apply_high_prefix_cylinder(high, count, precision + 1)
                assert high_precision % (10**precision) == low


def test_source_bound_cylinder_matches_additive_high_prefix() -> None:
    phase = C1Phase.from_suffix(5, 45)
    source = 5 * 10**14 + 45
    result = source_bound_return(source, phase, 83)
    for precision in range(25):
        assert result.high_cylinder(precision) == (
            result.source_high + result.count
        ) % (10**precision)


@pytest.mark.parametrize(
    "sector,suffix,steps",
    ((1, 1, 0), (1, 39, 7), (2, 54, 13), (5, 45, 9), (8, 73, 20), (9, 99, 0)),
)
def test_arbitrary_wire_lookup_matches_columnwise_addition(
    sector: int, suffix: int, steps: int
) -> None:
    high = sector * 10**12
    source = 100 * high + suffix
    phase = C1Phase.from_suffix(sector, suffix)
    result = source_bound_return(source, phase, steps)
    current_value = source + result.action.displacement()
    increment = 10 * result.target.ones + sector
    for wire in range(21):
        expected = _literal_addition_carry(current_value, increment, wire)
        assert result.carry_wire(wire) == expected
        assert carry_wire(result.target, result.target_high, wire) == expected


def test_long_trailing_nines_propagate_across_many_wires() -> None:
    high = 10**30 - 1
    source = 100 * high + 99
    phase = C1Phase.from_suffix(9, 99)
    result = source_bound_return(source, phase, 0)
    increment = 10 * result.target.ones + 9
    current_value = source + result.action.displacement()
    for wire in range(36):
        assert result.carry_wire(wire) == _literal_addition_carry(
            current_value, increment, wire
        )
    assert result.carry_wire(31)
    assert not result.carry_wire(32)


def test_huge_precision_is_resolved_before_decimal_power_allocation() -> None:
    precision = 10**100
    assert high_prefix_cylinder(12345, precision) == 12345
    assert apply_high_prefix_cylinder(12345, 678, precision) == 13023
    phase = C1Phase.from_suffix(1, 99)
    assert not carry_wire(phase, 12345, precision)
    charged: list[int] = []
    assert not carry_wire(
        phase,
        12345,
        precision,
        charge_bits=charged.append,
    )
    assert charged and max(charged) >= precision.bit_length()


def test_caller_budgets_are_charged_before_large_work_or_allocation() -> None:
    def reject_work(amount: int) -> None:
        if amount > 10:
            raise RuntimeError("work budget")

    def reject_bits(amount: int) -> None:
        if amount > 32:
            raise RuntimeError("operand budget")

    with pytest.raises(RuntimeError, match="operand budget"):
        C1Return(
            C1Phase.from_suffix(1, 2),
            10**20,
            charge_bits=reject_bits,
        )
    with pytest.raises(RuntimeError, match="work budget"):
        C1Return(
            C1Phase.from_suffix(1, 2),
            0,
            charge_work=reject_work,
        )
    with pytest.raises(RuntimeError, match="operand budget"):
        high_prefix_cylinder(10**100, 1, charge_bits=reject_bits)


def test_source_bound_composition_requires_both_endpoints() -> None:
    phase = C1Phase.from_suffix(5, 45)
    source = 5 * 10**13 + 45
    first = source_bound_return(source, phase, 2)
    middle_value = source + first.action.displacement()
    wrong_high = source_bound_return(middle_value + 100, first.target, 3)
    with pytest.raises(ValueError, match="not chronologically adjacent"):
        first.then(wrong_high)

    with pytest.raises(TypeError, match="source_bound_return"):
        BoundC1Return()


def test_huge_return_never_steps_and_charges_bounded_cycle_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    phase = C1Phase.from_suffix(7, 83)

    def forbidden_step(_self: C1Phase) -> C1Phase:
        pytest.fail("powered return replayed a primitive phase")

    monkeypatch.setattr(C1Phase, "step", forbidden_step)
    work_totals: list[int] = []
    bit_totals: list[int] = []
    for steps in (0, 10**3, 10**200):
        work: list[int] = []
        bits: list[int] = []
        result = C1Return(
            phase, steps, charge_work=work.append, charge_bits=bits.append
        )
        expected_suffix, expected_count = _periodic_oracle(7, 83, steps)
        assert (result.target.suffix, result.count) == (expected_suffix, expected_count)
        work_totals.append(sum(work))
        bit_totals.append(sum(bits))
    assert work_totals[0] == work_totals[1] == work_totals[2]
    assert bit_totals[0] < bit_totals[1] < bit_totals[2]


def test_nine_boundary_top_wire_retains_leading_occurrence() -> None:
    # N(2,5)=199999: stripping two digits leaves H=1999. The uniform
    # nine-tail shortcut applies through wire p-1; at wire p it is false.
    phase = C1Phase.from_suffix(1, 99)
    identity = C1Return(phase, 0)
    assert identity.count == 0
    assert phase.c1
    assert carry_wire(phase, 1999, 4)
    assert not carry_wire(phase, 1999, 5)
    assert _literal_addition_carry(199999, 91, 4)
    assert not _literal_addition_carry(199999, 91, 5)
