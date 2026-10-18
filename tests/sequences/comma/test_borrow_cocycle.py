from __future__ import annotations

from dataclasses import fields
from typing import NoReturn

import pytest

from number_compiler.sequences.comma import borrow_cocycle as borrow
from number_compiler.sequences.comma import carry_generator
from number_compiler.sequences.comma.carry_generator import (
    BoundC1Return,
    C1Phase,
    source_bound_return,
)


def _literal_suffix_step(sector: int, suffix: int) -> tuple[int, int]:
    """Add the local comma increment by decimal columns; return c1 as 0/1."""
    increment = 10 * (suffix % 10) + sector
    source = suffix
    carry = 0
    target = 0
    place = 1
    for _column in range(2):
        total = source % 10 + increment % 10 + carry
        target += (total % 10) * place
        carry = total // 10
        source //= 10
        increment //= 10
        place *= 10
    return target, carry


def _literal_pair_step(
    sector: int, delta: int, digit: int
) -> tuple[tuple[int, int], int]:
    """Use physical low-suffix additions to step one borrow state."""
    base_suffix = digit
    sibling_suffix = (base_suffix + delta) % 100
    next_base, base_c1 = _literal_suffix_step(sector, base_suffix)
    next_sibling, sibling_c1 = _literal_suffix_step(sector + 1, sibling_suffix)
    source_borrow = int(sibling_suffix < base_suffix)
    target_borrow = int(next_sibling < next_base)
    innovation = sibling_c1 - base_c1 + source_borrow - target_borrow
    return (
        (next_sibling - next_base) % 100,
        next_base % 10,
    ), innovation


def _periodic_oracle(
    sector: int, delta: int, digit: int, steps: int
) -> tuple[tuple[int, int], int]:
    """Independent finite-state cycle detection over literal additions."""
    initial = (delta, digit)
    seen: dict[tuple[int, int], int] = {}
    states: list[tuple[int, int]] = []
    outputs: list[int] = []
    current = initial
    while current not in seen:
        seen[current] = len(states)
        states.append(current)
        following, innovation = _literal_pair_step(sector, *current)
        outputs.append(innovation)
        current = following

    cycle_start = seen[current]
    if steps < len(states):
        return states[steps], sum(outputs[:steps])
    cycle_size = len(states) - cycle_start
    remaining = steps - cycle_start
    complete, tail = divmod(remaining, cycle_size)
    count = (
        sum(outputs[:cycle_start])
        + complete * sum(outputs[cycle_start:])
        + sum(outputs[cycle_start : cycle_start + tail])
    )
    target = states[cycle_start + tail]
    return target, count


def _source_bound_pair(
    sector: int,
    base_suffix: int,
    sibling_suffix: int,
    steps: int,
    *,
    base_high: int | None = None,
    sibling_high: int | None = None,
) -> tuple[BoundC1Return, BoundC1Return]:
    if base_high is None:
        base_high = sector * 10**12 + 123456
    if sibling_high is None:
        sibling_high = (sector + 1) * 10**12 + 654321
    base_phase = C1Phase.from_suffix(sector, base_suffix)
    sibling_phase = C1Phase.from_suffix(sector + 1, sibling_suffix)
    base = source_bound_return(100 * base_high + base_suffix, base_phase, steps)
    sibling = source_bound_return(
        100 * sibling_high + sibling_suffix,
        sibling_phase,
        steps,
    )
    return base, sibling


@pytest.mark.parametrize(
    ("field_name", "replacement"),
    (("sector", 5), ("delta", 12), ("digit", 5)),
)
def test_phase_has_only_the_three_local_pair_coordinates(
    field_name: str, replacement: int
) -> None:
    assert tuple(field.name for field in fields(borrow.BorrowPhase)) == (
        "sector",
        "delta",
        "digit",
    )
    phase = borrow.BorrowPhase.from_suffixes(4, 54, 65)
    assert phase == borrow.BorrowPhase(4, 11, 4)
    with pytest.raises((AttributeError, TypeError)):
        setattr(phase, field_name, replacement)


def test_exhaustive_one_step_innovation_matches_literal_column_additions() -> None:
    for sector in range(1, 9):
        for base_suffix in range(100):
            for sibling_suffix in range(100):
                phase = borrow.BorrowPhase.from_suffixes(
                    sector,
                    base_suffix,
                    sibling_suffix,
                )
                following, innovation = phase.step()
                next_base, base_c1 = _literal_suffix_step(sector, base_suffix)
                next_sibling, sibling_c1 = _literal_suffix_step(
                    sector + 1,
                    sibling_suffix,
                )
                source_borrow = int(sibling_suffix < base_suffix)
                target_borrow = int(next_sibling < next_base)
                expected_innovation = (
                    sibling_c1 - base_c1 + source_borrow - target_borrow
                )
                assert innovation == expected_innovation
                assert following == borrow.BorrowPhase.from_suffixes(
                    sector,
                    next_base,
                    next_sibling,
                )


@pytest.mark.parametrize(
    "sector,delta,digit",
    (
        (1, 99, 1),
        (2, 37, 6),
        (3, 0, 0),
        (4, 81, 4),
        (5, 54, 5),
        (6, 9, 9),
        (7, 45, 0),
        (8, 73, 8),
    ),
)
def test_powered_return_matches_independent_periodic_oracle(
    sector: int, delta: int, digit: int
) -> None:
    phase = borrow.BorrowPhase(sector, delta, digit)
    for steps in (0, 1, 17, 49, 50, 51, 117, 10**55 + 12345):
        expected_target, expected_innovation = _periodic_oracle(
            sector,
            delta,
            digit,
            steps,
        )
        result = borrow.BorrowReturn(phase, steps)
        assert (result.target.delta, result.target.digit) == expected_target
        assert result.innovation == expected_innovation
        assert result.target == phase.advance(steps)
        assert result.target == phase.advance(steps % 50)


def test_arbitrary_finite_powered_returns_match_literal_replay() -> None:
    for sector in (1, 4, 5, 8):
        for delta, digit in ((0, 0), (1, 1), (18, 8), (54, 5), (99, 9)):
            phase = borrow.BorrowPhase(sector, delta, digit)
            for steps in range(101):
                state = (delta, digit)
                total = 0
                for _ in range(steps):
                    state, innovation = _literal_pair_step(sector, *state)
                    total += innovation
                result = borrow.BorrowReturn(phase, steps)
                assert (result.target.delta, result.target.digit) == state
                assert result.innovation == total


def test_huge_return_does_not_replay_borrow_steps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sector, delta, digit = 5, 91, 3
    steps = 10**70 + 123456789
    expected_target, expected_innovation = _periodic_oracle(
        sector,
        delta,
        digit,
        steps,
    )

    def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError(
            "powered borrow construction replayed one-step transitions"
        )

    monkeypatch.setattr(borrow, "_one_step", forbidden)
    monkeypatch.setattr(borrow.BorrowPhase, "step", forbidden)
    monkeypatch.setattr(borrow.BorrowPhase, "advance", forbidden)
    result = borrow.BorrowReturn(borrow.BorrowPhase(sector, delta, digit), steps)
    assert (result.target.delta, result.target.digit) == expected_target
    assert result.innovation == expected_innovation


def test_chronological_composition_uses_child_innovations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    phase = borrow.BorrowPhase.from_suffixes(4, 54, 65)
    first_action = borrow.BorrowReturn(phase, 17)
    second_action = borrow.BorrowReturn(first_action.target, 29)
    whole_action = borrow.BorrowReturn(phase, 46)

    def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("borrow composition replayed the powered orbit")

    monkeypatch.setattr(borrow, "_powered_return_summary", forbidden)
    joined_action = first_action.then(second_action)
    assert (
        joined_action.start,
        joined_action.target,
        joined_action.steps,
        joined_action.innovation,
    ) == (
        whole_action.start,
        whole_action.target,
        whole_action.steps,
        whole_action.innovation,
    )


def test_bound_difference_reconstructs_sibling_high_and_composes_warm(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    base, sibling = _source_bound_pair(4, 54, 65, 7)
    first = borrow.bind_borrow_return(base, sibling)
    middle_base_value = 100 * base.target_high + base.target.suffix
    middle_sibling_value = 100 * sibling.target_high + sibling.target.suffix
    next_base = source_bound_return(
        middle_base_value,
        base.target,
        11,
    )
    next_sibling = source_bound_return(
        middle_sibling_value,
        sibling.target,
        11,
    )
    second = borrow.bind_borrow_return(next_base, next_sibling)

    direct_base, direct_sibling = _source_bound_pair(
        4,
        54,
        65,
        18,
        base_high=base.source_high,
        sibling_high=sibling.source_high,
    )
    direct = borrow.bind_borrow_return(direct_base, direct_sibling)

    def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("warm paired composition recomputed a powered owner")

    monkeypatch.setattr(borrow, "_powered_return_summary", forbidden)
    monkeypatch.setattr(
        carry_generator,
        "_fixed_sector_displacement",
        forbidden,
    )
    joined = first.then(second)
    assert joined.action.steps == direct.action.steps
    assert joined.action.innovation == direct.action.innovation
    assert joined.action.target == direct.action.target
    assert joined.base.target_high == direct.base.target_high
    assert joined.sibling.target_high == direct.sibling.target_high
    assert joined.reconstruct_sibling_high(joined.base.target_high) == (
        joined.sibling.target_high
    )
    assert (
        joined.sibling.target_high - joined.base.target_high - joined.target_borrow
    ) == joined.normalized_high_difference() + joined.action.innovation


def test_bind_rejects_nonadjacent_sectors_or_unequal_durations() -> None:
    base, _sibling = _source_bound_pair(3, 28, 41, 4)
    wrong_sector = source_bound_return(
        6 * 10**14 + 41,
        C1Phase.from_suffix(6, 41),
        4,
    )
    with pytest.raises(ValueError, match="adjacent sectors"):
        borrow.bind_borrow_return(base, wrong_sector)

    shorter = source_bound_return(
        4 * 10**14 + 41,
        C1Phase.from_suffix(4, 41),
        3,
    )
    with pytest.raises(ValueError, match="equal durations"):
        borrow.bind_borrow_return(base, shorter)


def test_returns_reject_invalid_and_forged_states() -> None:
    with pytest.raises(ValueError, match="borrow suffixes"):
        borrow.BorrowPhase.from_suffixes(9, 0, 0)
    with pytest.raises(ValueError, match="nonnegative"):
        borrow.BorrowReturn(borrow.BorrowPhase(2, 3, 4), -1)

    action = borrow.BorrowReturn(borrow.BorrowPhase(2, 3, 4), 1)
    object.__setattr__(action, "_innovation", 1)
    with pytest.raises(ValueError, match="snapshot"):
        _ = action.innovation

    base, sibling = _source_bound_pair(5, 45, 54, 3)
    bound = borrow.bind_borrow_return(base, sibling)
    object.__setattr__(bound, "_source_borrow", 1 - bound.source_borrow)
    with pytest.raises(ValueError, match="snapshot"):
        _ = bound.action


def test_caller_budgets_are_checked_before_powering() -> None:
    phase = borrow.BorrowPhase(4, 73, 1)

    def reject_work(amount: int) -> None:
        if amount > 10:
            raise RuntimeError("work budget")

    def reject_bits(amount: int) -> None:
        if amount > 64:
            raise RuntimeError("operand budget")

    with pytest.raises(RuntimeError, match="work budget"):
        borrow.BorrowReturn(phase, 0, charge_work=reject_work)
    with pytest.raises(RuntimeError, match="operand budget"):
        borrow.BorrowReturn(phase, 10**100, charge_bits=reject_bits)


def test_base_high_reconstruction_requires_exact_bound_endpoint() -> None:
    base, sibling = _source_bound_pair(2, 19, 37, 5)
    result = borrow.bind_borrow_return(base, sibling)
    with pytest.raises(ValueError, match="does not match"):
        result.reconstruct_sibling_high(base.target_high + 1)


def test_zero_length_borrow_binding_preserves_initial_difference() -> None:
    base, sibling = _source_bound_pair(8, 99, 0, 0)
    result = borrow.bind_borrow_return(base, sibling)
    assert result.action.innovation == 0
    assert result.source_borrow == 1
    assert result.target_borrow == 1
    assert result.reconstruct_sibling_high(base.target_high) == sibling.target_high
