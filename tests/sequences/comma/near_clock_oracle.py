"""Independent Euclidean first-event clock for bounded Near headrooms."""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Literal

from tests.sequences.comma.padic_event_oracle import exact_integer

NearTerminalKind = Literal["Fork", "SectorCross", "DecadeCross", "Landmine"]
NearActionKind = Literal["Continue", "Fork", "SectorCross", "DecadeCross", "Landmine"]


@dataclass(frozen=True, slots=True)
class NearEventClock:
    elapsed_steps: int
    residual_headroom: int
    terminal_kind: NearTerminalKind
    terminal_digit: int


@dataclass(frozen=True, slots=True)
class NearImmediateAction:
    kind: NearActionKind
    next_headroom: int | None


def _validated_near(leading: int, headroom: int) -> tuple[int, int]:
    sector = exact_integer(leading, "leading")
    value = exact_integer(headroom, "headroom")
    if not 1 <= sector <= 9 or not 1 <= value <= 540:
        raise ValueError("Near clock requires leading 1..9 and headroom 1..540")
    return sector, value


def _terminal_kind(leading: int, headroom: int) -> NearTerminalKind:
    digit = (-headroom) % 10
    increment = 10 * digit + leading
    extra = int(leading < 9)
    if headroom > increment + extra:
        raise ValueError("headroom is not at a decisive Near event")
    if leading < 9:
        return "Fork" if headroom == increment + extra else "SectorCross"
    return "DecadeCross" if headroom <= 10 * digit + 1 else "Landmine"


def near_event_clock(leading: int, headroom: int) -> NearEventClock:
    """Exact Euclidean clock to the first decisive Near event.

    The formal event parameter ``headroom`` remains a bound input. The cycle
    quotient and residual are derived outputs, not class identifiers.
    """
    sector, value = _validated_near(leading, headroom)
    extra = int(sector < 9)
    if value <= extra:
        return NearEventClock(0, value, _terminal_kind(sector, value), (-value) % 10)

    digit = (-value) % 10
    cycle_length = 10 // gcd(sector, 10)
    increments = tuple(
        10 * ((digit + index * sector) % 10) + sector for index in range(cycle_length)
    )
    displacement = sum(increments)
    whole_cycles, remainder = divmod(value - extra - 1, displacement)
    prefix = [0]
    for increment in increments:
        prefix.append(prefix[-1] + increment)
    tail = max(index for index in range(cycle_length) if prefix[index] <= remainder)
    residual = value - whole_cycles * displacement - prefix[tail]
    terminal_kind = _terminal_kind(sector, residual)
    return NearEventClock(
        whole_cycles * cycle_length + tail,
        residual,
        terminal_kind,
        (-residual) % 10,
    )


def direct_near_event_clock(leading: int, headroom: int) -> NearEventClock:
    """Literal reference bounded by the initial positive integer headroom."""
    sector, current = _validated_near(leading, headroom)
    for elapsed in range(current + 1):
        digit = (-current) % 10
        increment = 10 * digit + sector
        if sector < 9 and current <= increment + 1:
            kind: NearTerminalKind = (
                "Fork" if current == increment + 1 else "SectorCross"
            )
            return NearEventClock(
                elapsed,
                current,
                kind,
                digit,
            )
        if sector == 9 and current <= increment:
            kind = "DecadeCross" if current <= 10 * digit + 1 else "Landmine"
            return NearEventClock(elapsed, current, kind, digit)
        following = current - increment
        if following <= 0 or following >= current:
            raise AssertionError("strict Near continuation failed to decrease H")
        current = following
    raise AssertionError(
        "positive H decreases by at least one per Continue, so the initial H bound suffices"
    )


def near_immediate_action(leading: int, headroom: int) -> NearImmediateAction:
    """Return the first typed action, preserving Continue versus terminals."""
    sector, value = _validated_near(leading, headroom)
    digit = (-value) % 10
    increment = 10 * digit + sector
    if value > increment + int(sector < 9):
        return NearImmediateAction("Continue", value - increment)
    return NearImmediateAction(_terminal_kind(sector, value), None)
