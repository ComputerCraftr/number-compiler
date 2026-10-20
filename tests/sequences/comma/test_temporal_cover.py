"""Independent checks for the finite comma temporal cover and weighted jumps."""

from __future__ import annotations

import builtins
from typing import Never

import pytest

from devtools.verification.comma_pair_language import pair_block_levels
from number_compiler.sequences.comma import temporal_cover
from number_compiler.sequences.comma.temporal_cover import (
    PortDyadicTime,
    PortTime,
    TemporalPortCover,
    advance_temporal_cover,
    advance_weighted_port,
    apply_dyadic_time,
    apply_port_time,
    compose_port_times,
    dyadic_time_for_level,
    dyadic_time_semantics,
    port_time_for_duration,
    square_dyadic_time,
)


def _literal_next(leading: int, digit: int) -> int:
    previous = (digit + 10 - leading) % 10
    return (previous + 10 - leading) % 10 if previous == 0 else previous


def _literal_dwell(leading: int, digit: int) -> int:
    if leading == 9:
        return digit + 1
    return digit + int(9 - leading <= digit < 9)


def _literal_advance(leading: int, digit: int, steps: int) -> int:
    current = digit
    for _ in range(steps):
        current = _literal_next(leading, current)
    return current


def _literal_cycle_advance(leading: int, digit: int, steps: int) -> int:
    if steps == 0:
        return digit
    first = _literal_next(leading, digit)
    cycle: list[int] = []
    current = first
    while current not in cycle:
        cycle.append(current)
        current = _literal_next(leading, current)
    assert current == first
    return cycle[(steps - 1) % len(cycle)]


def _literal_weight(leading: int, digit: int, steps: int) -> tuple[int, int]:
    if steps == 0:
        return digit, 0
    first = _literal_next(leading, digit)
    cycle: list[int] = []
    current = first
    while current not in cycle:
        cycle.append(current)
        current = _literal_next(leading, current)
    assert current == first
    cycles, tail = divmod(steps - 1, len(cycle))
    endpoint = cycle[tail]
    weight = _literal_dwell(leading, digit)
    weight += cycles * sum(_literal_dwell(leading, value) for value in cycle)
    weight += sum(_literal_dwell(leading, value) for value in cycle[:tail])
    return endpoint, weight


def _literal_q21_reset(
    leading: int, digit: int, steps: int
) -> tuple[int | None, int, int, int | None, int]:
    domain: int | None = None
    parity = 0
    affine_five = 0
    reset: int | None = None
    phase = 1
    current = digit
    for _ in range(steps):
        previous = (current + 10 - leading) % 10
        pair_sum = current + previous
        defect = pair_sum - 9
        if defect:
            domain = -1 if defect < 0 else 1
            reset = (-abs(defect)) % 5
        parity = (parity + defect) % 2
        affine_five = (affine_five + defect * phase) % 5
        phase = (2 * phase) % 5
        current = _literal_next(leading, current)
    return domain, parity, affine_five, reset, current


def test_cover_is_exactly_the_86_keys_with_four_two_sheet_fibers() -> None:
    covers = {
        TemporalPortCover.from_port(leading, digit)
        for leading in range(1, 10)
        for digit in range(10)
    }
    assert len(covers) == 90
    assert len({cover.even_key for cover in covers}) == 86
    assert TemporalPortCover.from_port(5, 1).sheet is False
    assert TemporalPortCover.from_port(5, 6).sheet is True
    for cover in covers:
        assert TemporalPortCover.from_port(cover.leading, cover.digit) == cover
        assert cover.centered_defect == (
            cover.digit + (cover.digit + 10 - cover.leading) % 10 - 9
        )
    doubletons = {
        (cover.leading, cover.folded_digit)
        for cover in covers
        if sum(other.even_key == cover.even_key for other in covers) == 2
    }
    assert doubletons == {(5, digit) for digit in range(1, 5)}
    assert sum(cover.even_key == (5, 1) for cover in covers) == 2


def test_temporal_cover_step_matches_literal_ports_and_sheet_law() -> None:
    for leading in range(1, 10):
        for digit in range(10):
            cover = TemporalPortCover.from_port(leading, digit)
            expected = _literal_next(leading, digit)
            assert cover.step().digit == expected
            assert cover.step().centered_defect == (
                expected + (expected + 10 - leading) % 10 - 9
            )
    for digit in range(1, 5):
        lower = TemporalPortCover.from_port(5, digit)
        upper = TemporalPortCover.from_port(5, digit + 5)
        assert lower.even_key == upper.even_key
        assert lower.step().even_key == lower.even_key
        assert upper.step().even_key == upper.even_key
        assert lower.step().sheet is True
        assert upper.step().sheet is False
        assert lower.step().step() == lower
        assert upper.step().step() == upper


def test_port_time_monoid_matches_literal_duration_classes() -> None:
    for left_duration in range(181):
        left = port_time_for_duration(left_duration)
        if left_duration:
            assert left == port_time_for_duration(left_duration + 180)
        for right_duration in (0, 1, 2, 4, 9, 179, 180, 181):
            right = port_time_for_duration(right_duration)
            combined = compose_port_times(left, right)
            assert combined == port_time_for_duration(left_duration + right_duration)
    for leading in range(1, 10):
        for digit in range(10):
            for duration in range(182):
                action = port_time_for_duration(duration)
                assert apply_port_time(leading, digit, action) == _literal_advance(
                    leading, digit, duration
                )


def test_large_temporal_classes_and_dyadic_squaring_are_bounded() -> None:
    huge = 10**100 + 123456789
    action = port_time_for_duration(huge)
    assert action == port_time_for_duration(huge + 180 * 10**80)
    for leading in range(1, 10):
        for digit in range(10):
            assert action.positive_offset is not None
            assert apply_port_time(leading, digit, action) == _literal_cycle_advance(
                leading, digit, huge
            )
    for level in range(40):
        dyadic = dyadic_time_for_level(level)
        if level >= 2:
            assert dyadic == dyadic_time_for_level(level + 12)
        assert dyadic_time_semantics(dyadic) == port_time_for_duration(2**level)
        assert square_dyadic_time(dyadic) == dyadic_time_for_level(level + 1)
        for leading in range(1, 10):
            for digit in range(10):
                cover = TemporalPortCover.from_port(leading, digit)
                result = apply_dyadic_time(cover, dyadic)
                expected = (
                    _literal_advance(leading, digit, 2**level)
                    if level <= 10
                    else _literal_cycle_advance(leading, digit, 2**level)
                )
                assert result.digit == expected
                assert (
                    advance_temporal_cover(cover, dyadic_time_semantics(dyadic))
                    == result
                )
    assert dyadic_time_for_level(10**100).code in range(14)


def test_theta_181_classes_are_distinguished_by_exact_port_actions() -> None:
    witnesses = ((1, 0), (1, 1), (2, 1), (2, 2))
    actions = (PortTime(None), *(PortTime(offset) for offset in range(180)))
    signatures = {
        tuple(apply_port_time(f, d, action) for f, d in witnesses) for action in actions
    }
    assert len(signatures) == 181


def test_theta_14_dyadic_classes_are_distinct_on_the_physical_cover() -> None:
    ports = tuple((f, d) for f in range(1, 10) for d in range(10))
    signatures = {
        tuple(
            apply_dyadic_time(
                TemporalPortCover.from_port(f, d), PortDyadicTime(code)
            ).digit
            for f, d in ports
        )
        for code in range(14)
    }
    assert len(signatures) == 14


def test_temporal_cover_regenerates_bounded_pair_macro_endpoints_and_midpoints() -> (
    None
):
    for level, blocks in enumerate(pair_block_levels(10)):
        for block in blocks:
            source = TemporalPortCover.from_port(block.leading, block.source)
            end = apply_dyadic_time(source, dyadic_time_for_level(level))
            assert end.digit == block.endpoint
            if level:
                middle = advance_temporal_cover(
                    source, port_time_for_duration(block.width // 2)
                )
                assert middle.digit == _literal_advance(
                    block.leading, block.source, block.width // 2
                )


@pytest.mark.parametrize(
    "steps",
    (0, 1, 2, 3, 8, 9, 10, 179, 180, 181, 359, 360, 1000, 2**20, 10**100 + 7),
)
def test_weighted_temporal_factorization_matches_independent_cycle_oracle(
    steps: int,
) -> None:
    for leading in range(1, 10):
        for digit in range(10):
            result = advance_weighted_port(leading, digit, steps)
            assert (result.endpoint, result.weight) == _literal_weight(
                leading, digit, steps
            )
            assert result.tail_steps < 9
            assert result.complete_cycles >= 0


def test_weighted_large_jump_charges_bounded_construction_and_tail_work() -> None:
    work = 0
    bit_work = 0

    def charge_work(amount: int) -> None:
        nonlocal work
        work += amount

    def charge_bits(amount: int) -> None:
        nonlocal bit_work
        bit_work += amount

    result = advance_weighted_port(
        5,
        6,
        10**100,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    assert result.tail_steps < 9
    assert work <= 17
    assert bit_work >= (10**100).bit_length()


def test_same_theta_endpoint_keeps_the_exact_weighted_occurrence() -> None:
    zero = advance_weighted_port(1, 1, 0)
    full_period = advance_weighted_port(1, 1, 180)
    assert zero.endpoint == full_period.endpoint == 1
    assert zero.weight == 0
    assert full_period.weight == 920
    repeated_period = advance_weighted_port(1, 1, 360)
    assert port_time_for_duration(180) == port_time_for_duration(360)
    assert repeated_period.endpoint == full_period.endpoint == 1
    assert repeated_period.weight == 1840


def test_reported_q21_and_reset_transient_witnesses_are_literal() -> None:
    first, first_period_copy = (
        _literal_q21_reset(1, 0, 1),
        _literal_q21_reset(1, 0, 13_861),
    )
    assert first[1:3] == first_period_copy[1:3] == (0, 0)
    assert first[0] is None and first_period_copy[0] == -1
    assert first[3] is None and first_period_copy[3] == 2
    assert first[4] == first_period_copy[4] == 9

    second, second_period_copy = (
        _literal_q21_reset(7, 0, 2),
        _literal_q21_reset(7, 0, 13_862),
    )
    assert second[:3] == second_period_copy[:3]
    assert second[0] == -1
    assert second[3] == 4 and second_period_copy[3] == 3
    assert second[4] == second_period_copy[4] == 6


def test_budget_refusal_happens_before_cycle_work_or_large_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def refused(_: int) -> None:
        raise RuntimeError("budget refused")

    def forbidden_cycle_transfer(*_args: object, **_kwargs: object) -> Never:
        pytest.fail("cycle arithmetic ran before budget admission")

    monkeypatch.setattr(temporal_cover, "cycle_transfer", forbidden_cycle_transfer)
    with pytest.raises(RuntimeError, match="budget refused"):
        advance_weighted_port(5, 6, 10**100, charge_work=refused)

    def forbidden_power(*_args: object, **_kwargs: object) -> Never:
        pytest.fail("dyadic power ran before budget admission")

    monkeypatch.setattr(builtins, "pow", forbidden_power)
    with pytest.raises(RuntimeError, match="budget refused"):
        dyadic_time_semantics(PortDyadicTime(13), charge_work=refused)


@pytest.mark.parametrize(
    ("leading", "digit"), ((0, 1), (10, 1), (5, -1), (5, 10), (True, 1))
)
def test_cover_rejects_nonphysical_ports(leading: int, digit: int) -> None:
    with pytest.raises(ValueError, match="leading 1..9"):
        TemporalPortCover.from_port(leading, digit)


@pytest.mark.parametrize(
    "cover", ((5, 5, False), (5, 6, False), (5, 0, True), (4, 9, False))
)
def test_cover_rejects_forged_or_inconsistent_sheets(
    cover: tuple[int, int, bool],
) -> None:
    with pytest.raises(ValueError):
        TemporalPortCover(*cover)


@pytest.mark.parametrize("duration", (-1, True, 1.5))
def test_time_encoding_rejects_invalid_durations(duration: int) -> None:
    with pytest.raises(ValueError, match="nonnegative integer"):
        port_time_for_duration(duration)


@pytest.mark.parametrize("value", (-1, 180, True, 1.5))
def test_time_actions_reject_noncanonical_offsets(value: int) -> None:
    with pytest.raises(ValueError, match="offset"):
        PortTime(value)


@pytest.mark.parametrize("code", (-1, 14, True, 1.5))
def test_dyadic_actions_reject_noncanonical_codes(code: int) -> None:
    with pytest.raises(ValueError, match="code"):
        PortDyadicTime(code)


def test_resource_callbacks_are_optional_and_receive_actual_weighted_work() -> None:
    work: list[int] = []
    bits: list[int] = []
    direct = advance_weighted_port(3, 7, 1_000_003)
    charged = advance_weighted_port(
        3,
        7,
        1_000_003,
        charge_work=work.append,
        charge_bits=bits.append,
    )
    assert charged == direct
    assert sum(work) <= 17
    assert sum(bits) > 0


def test_identity_cover_application_reuses_admitted_object() -> None:
    cover = TemporalPortCover.from_port(5, 6)
    work: list[int] = []
    assert (
        advance_temporal_cover(cover, PortTime(None), charge_work=work.append) is cover
    )
    assert work == [1]
