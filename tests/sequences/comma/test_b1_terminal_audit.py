"""Cheap geometry checks for the independent B1 terminal-control audit."""

from __future__ import annotations

from dataclasses import asdict
from typing import Protocol, cast

import pytest

import devtools.verification.comma_b1_terminal_audit as terminal_audit
from devtools.verification.comma_b1_terminal_audit import (
    EXPECTED_FORK_COUNTS,
    EXPECTED_LANDMINE_COUNT,
    EXPECTED_LANDMINE_HEADROOMS,
    FULL_B1_COUNT,
    StopD,
    TerminalControl,
    decode_stop_d,
    eventual_stop,
    full_audit_command,
    full_future_audit_command,
    terminal_control,
)
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    near_chart_target,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.decisive_endpoint import DecisiveEndpoint


class _StopSourceAssertion(Protocol):
    def __call__(
        self,
        stop: StopD,
        actual_kind: str,
        actual_fork_a: int | None,
        *,
        actual_complete_decades: int,
        actual_within_decade: int,
    ) -> None: ...


_assert_stop_matches_source = cast(
    _StopSourceAssertion,
    object.__getattribute__(terminal_audit, "_assert_stop_matches_source"),
)


@pytest.mark.parametrize("fork_a", range(2, 10))
def test_fork_terminal_position_is_a_minus_one_and_j_is_a_minus_two(
    fork_a: int,
) -> None:
    terminal_sector = fork_a - 1
    # The active digit 9-terminal is the exact equality h=10*d+f+1 with
    # d=9-f.  This derives the position law from the Near seam classifier.
    headroom = 91 - 9 * terminal_sector
    endpoint = DecisiveEndpoint(terminal_sector, headroom)
    move = near_chart_target(
        BoundaryChart("near", endpoint.sector, 0, endpoint.headroom)
    )
    assert move.next_chart is None
    assert move.fork_a == fork_a
    result = TerminalControl(
        "fork",
        endpoint.sector,
        endpoint.headroom,
        move.fork_a,
        0,
        endpoint.sector - 1,
        0,
        0,
    )
    assert result.within_decade == fork_a - 2


def test_landmine_headrooms_are_sector_nine_seam_positions() -> None:
    for headroom in EXPECTED_LANDMINE_HEADROOMS:
        endpoint = DecisiveEndpoint(9, headroom)
        move = near_chart_target(
            BoundaryChart("near", endpoint.sector, 0, endpoint.headroom)
        )
        assert move.next_chart is None
        assert move.fork_a is None
        result = TerminalControl(
            "landmine",
            endpoint.sector,
            endpoint.headroom,
            None,
            0,
            endpoint.sector - 1,
            0,
            0,
        )
        assert result.terminal_sector == 9


def test_landmine_terminal_requires_j_eight() -> None:
    with pytest.raises(AssertionError, match="invalid landmine terminal control"):
        TerminalControl("landmine", 9, 19, None, 0, 7, 0, 0)


def test_source_control_keeps_complete_decade_and_crossing_weight_separate() -> None:
    live = terminal_control(CyclotomicClock.from_phase(0), 0)
    assert live.kind == "live"
    assert live.complete_decades == 1
    assert live.literal_transition_weight == 1
    assert live.fork_a is None


def test_full_terminal_population_is_explicitly_opt_in() -> None:
    assert FULL_B1_COUNT == 42_504
    assert EXPECTED_FORK_COUNTS == {
        2: 924,
        3: 924,
        4: 924,
        5: 616,
        6: 770,
        7: 924,
        8: 672,
        9: 753,
    }
    assert EXPECTED_LANDMINE_COUNT == 5_766
    assert full_audit_command().endswith("comma_b1_terminal_audit --full")


def test_stop_d_decodes_only_the_source_transition_encoding() -> None:
    fork = decode_stop_d(9 * 5 + 2)
    assert (fork.complete_decades, fork.within_decade) == (5, 2)
    assert (fork.kind, fork.fork_a) == ("fork", 4)

    landmine = decode_stop_d(9 * 5 + 8)
    assert (landmine.complete_decades, landmine.within_decade) == (5, 8)
    assert (landmine.kind, landmine.fork_a) == ("landmine", None)


def test_stop_d_audit_compares_an_independent_source_terminal() -> None:
    stop = decode_stop_d(9 * 26 + 3)
    _assert_stop_matches_source(
        stop,
        "fork",
        5,
        actual_complete_decades=26,
        actual_within_decade=3,
    )
    with pytest.raises(AssertionError, match="source terminal"):
        _assert_stop_matches_source(
            stop,
            "landmine",
            None,
            actual_complete_decades=26,
            actual_within_decade=3,
        )
    with pytest.raises(AssertionError, match="source transition counts"):
        _assert_stop_matches_source(
            stop,
            "fork",
            5,
            actual_complete_decades=25,
            actual_within_decade=3,
        )


def test_full_future_audit_is_explicitly_opt_in() -> None:
    assert full_future_audit_command().endswith("comma_b1_terminal_audit --full-future")


def test_sharp_stop_weight_is_constructed_from_source_transitions() -> None:
    clock = CyclotomicClock.from_phase(42)
    stop = eventual_stop(clock, 68)
    assert asdict(stop) == {"d": 237}
    assert (stop.complete_decades, stop.within_decade) == (26, 3)
    assert (stop.kind, stop.fork_a) == ("fork", 5)
    with pytest.raises(RuntimeError, match="bounded decade horizon"):
        eventual_stop(clock, 68, max_complete_decades=25)


@pytest.mark.parametrize("d", [-1, True, 297])
def test_stop_weight_rejects_invalid_bounded_encodings(d: int) -> None:
    with pytest.raises(ValueError, match=r"Stop\(D\)"):
        decode_stop_d(d)
