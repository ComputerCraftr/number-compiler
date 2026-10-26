"""Independent parameterized Near event-clock regressions."""

from __future__ import annotations

import pytest

from tests.sequences.comma.near_clock_oracle import (
    direct_near_event_clock,
    near_event_clock,
    near_immediate_action,
)


def test_h82_fork_and_h92_continue_are_distinct_typed_actions() -> None:
    fork = near_immediate_action(1, 82)
    continued = near_immediate_action(1, 92)
    fork_clock = near_event_clock(1, 82)
    continued_clock = near_event_clock(1, 92)

    assert (fork.kind, fork.next_headroom) == ("Fork", None)
    assert (continued.kind, continued.next_headroom) == ("Continue", 11)
    assert (fork_clock.elapsed_steps, fork_clock.residual_headroom) == (0, 82)
    assert fork_clock.terminal_kind == "Fork"
    assert (continued_clock.elapsed_steps, continued_clock.residual_headroom) == (
        1,
        11,
    )
    assert continued_clock.terminal_kind == "SectorCross"


@pytest.mark.parametrize(
    ("leading", "headroom"),
    [(1, 82), (1, 92), (2, 73), (8, 91), (9, 19), (9, 540)],
)
def test_near_clock_representatives_match_direct_first_event(
    leading: int, headroom: int
) -> None:
    assert near_event_clock(leading, headroom) == direct_near_event_clock(
        leading, headroom
    )


@pytest.mark.validation
def test_all_4860_near_sector_headrooms_match_the_literal_first_hit() -> None:
    checked = 0
    for leading in range(1, 10):
        for headroom in range(1, 541):
            assert near_event_clock(leading, headroom) == direct_near_event_clock(
                leading, headroom
            )
            checked += 1
    assert checked == 4_860


@pytest.mark.parametrize(
    ("leading", "headroom", "error"),
    [
        (True, 82, TypeError),
        (1, False, TypeError),
        (0, 82, ValueError),
        (10, 82, ValueError),
        (1, 0, ValueError),
        (1, 541, ValueError),
    ],
)
def test_near_clock_rejects_invalid_exact_inputs(
    leading: int, headroom: int, error: type[Exception]
) -> None:
    with pytest.raises(error):
        near_event_clock(leading, headroom)
