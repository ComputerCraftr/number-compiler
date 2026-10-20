"""Run-level decimal pair temporal square used by the Q19 image owner.

The operation here is the authenticated fixed-depth T2/T4 pullback from the
NC10 punctured-carry construction.  It consumes and returns maximal run tapes;
the caller owns source authority, ledger reservations, occurrence publication,
and any larger temporal composition.  This module deliberately contains no
global memo and makes no all-depth quotient claim.
"""

from __future__ import annotations

from bisect import bisect_left
from collections.abc import Sequence
from dataclasses import dataclass
from itertools import pairwise

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.fields.run_pairing import pair_mirror_digit_runs


@dataclass(slots=True)
class PuncturedTemporalWork:
    """Actual run-record work performed by one bounded temporal pullback."""

    run_records_visited: int = 0
    prefix_queries: int = 0
    event_regions: int = 0
    output_runs: int = 0


def append_run(target: list[tuple[int, int]], symbol: int, count: int) -> None:
    if count <= 0:
        return
    if target and target[-1][0] == symbol:
        target[-1] = (symbol, target[-1][1] + count)
    else:
        target.append((symbol, count))


class CarryPrefix:
    """Exact carry transfer at run boundaries, with logarithmic point lookup."""

    __slots__ = ("_switches", "effects", "ends", "runs", "work")

    def __init__(
        self, runs: Sequence[tuple[int, int]], work: PuncturedTemporalWork
    ) -> None:
        self.work = work
        canonical: list[tuple[int, int]] = []
        ends: list[int] = []
        effects = [CarryFn.ID]
        switches: list[int] = []
        end = 0
        carry = 0
        for symbol, count in runs:
            work.run_records_visited += 1
            if type(count) is not int or count <= 0:
                raise ValueError("carry tape requires positive exact run lengths")
            transfer = value_carry_fn(symbol, 10)
            end += count
            if canonical and canonical[-1][0] == symbol:
                previous_symbol, previous_count = canonical[-1]
                canonical[-1] = (previous_symbol, previous_count + count)
                ends[-1] = end
                continue
            following = apply_carry_fn(transfer, carry)
            if following != carry:
                switches.append(end - count + 1)
            carry = following
            canonical.append((symbol, count))
            ends.append(end)
            effects.append(compose_carry_fn(transfer, effects[-1]))
        self.runs = tuple(canonical)
        self.ends = tuple(ends)
        self.effects = tuple(effects)
        self._switches = tuple(switches)

    @property
    def width(self) -> int:
        return self.ends[-1] if self.ends else 0

    def carry_at(self, offset: int) -> int:
        self.work.prefix_queries += 1
        if type(offset) is not int or not 0 <= offset <= self.width:
            raise IndexError(offset)
        if offset == 0:
            return 0
        index = bisect_left(self.ends, offset)
        return apply_carry_fn(self.effects[index + 1], 0)

    def switch_offsets(self) -> tuple[int, ...]:
        return self._switches

    def symbol_at(self, index: int) -> int:
        self.work.prefix_queries += 1
        if type(index) is not int or not 0 <= index < self.width:
            raise IndexError(index)
        return self.runs[bisect_left(self.ends, index + 1)][0]

    def emitted_digit_runs(self) -> tuple[tuple[tuple[int, int], ...], int]:
        carry = 0
        output: list[tuple[int, int]] = []
        for symbol, count in self.runs:
            self.work.run_records_visited += 1
            following = apply_carry_fn(value_carry_fn(symbol, 10), carry)
            append_run(output, symbol + carry - 10 * following, 1)
            if count > 1:
                append_run(output, symbol + following - 10 * following, count - 1)
            carry = following
        return tuple(output), carry


def _palindromic_runs(
    half_runs: Sequence[tuple[int, int]],
    *,
    odd: bool,
    work: PuncturedTemporalWork,
) -> tuple[tuple[int, int], ...]:
    if not half_runs:
        raise ValueError("positive pair output requires a nonempty half")
    result = list(half_runs)
    work.run_records_visited += len(half_runs)
    last = len(half_runs) - 1
    for index in range(last, -1, -1):
        work.run_records_visited += 1
        symbol, count = half_runs[index]
        if odd and index == last:
            count -= 1
        append_run(result, symbol, count)
    return tuple(result)


def _paired_half_runs(
    digit_runs: Sequence[tuple[int, int]],
    work: PuncturedTemporalWork,
) -> tuple[tuple[tuple[int, int], ...], bool]:
    paired, odd, visits = pair_mirror_digit_runs(digit_runs, half_only=True)
    work.run_records_visited += visits
    return paired, odd


def one_two_step_pair(
    source_runs: Sequence[tuple[int, int]],
    work: PuncturedTemporalWork,
) -> tuple[tuple[tuple[int, int], ...], int]:
    """Return pair-half runs after one exact two-step pair transition."""
    source = CarryPrefix(source_runs, work)
    width = source.width
    if width < 1:
        raise ValueError("source pair tape must be nonempty")
    ingress = source.carry_at(width)
    first_width = width + ingress

    # Event positions include source, carry-reset, reflected, and endpoint
    # boundaries.  The two-cell halos cover the local stencil's full radius.
    positions = {0, first_width}

    def surround(boundary: int) -> None:
        for delta in (-2, -1, 0, 1, 2):
            position = boundary + delta
            if 0 <= position <= first_width:
                positions.add(position)

    surround(0)
    surround(width)
    for boundary in source.ends:
        surround(boundary)
        surround(width - boundary)
    for boundary in source.switch_offsets():
        surround(boundary)
        surround(width - boundary)
    ordered = sorted(positions)
    work.event_regions += max(0, len(ordered) - 1)

    def coefficient(index: int) -> int:
        carry = source.carry_at
        symbol = source.symbol_at
        if ingress:
            if index in (0, width):
                return symbol(0) + 1 - 10 * carry(1)
            return (
                symbol(index - 1)
                + symbol(index)
                + carry(index)
                + carry(width - index)
                - 10 * (carry(index + 1) + carry(width - index + 1))
            )
        return (
            2 * symbol(index)
            + carry(index)
            + carry(width - 1 - index)
            - 10 * (carry(index + 1) + carry(width - index))
        )

    temporal_runs: list[tuple[int, int]] = []
    for start, end in pairwise(ordered):
        work.run_records_visited += 1
        if start == end:
            continue
        value = coefficient(start)
        if not 0 <= value <= 18:
            raise ValueError("carry event partition failed exact local validation")
        if end - start > 1 and coefficient(end - 1) != value:
            raise ValueError("carry event partition failed exact local validation")
        append_run(temporal_runs, value, end - start)

    normalized_prefix = CarryPrefix(temporal_runs, work)
    digit_runs, final_carry = normalized_prefix.emitted_digit_runs()
    if final_carry:
        mutable_digits = list(digit_runs)
        append_run(mutable_digits, 1, 1)
        digit_runs = tuple(mutable_digits)
    pairs, _odd = _paired_half_runs(digit_runs, work)
    work.output_runs += len(pairs)
    return pairs, normalized_prefix.width + final_carry


def punctured_pair_runs(
    half_runs: Sequence[tuple[int, int]],
    *,
    odd: bool,
    steps: int,
    work: PuncturedTemporalWork,
) -> tuple[tuple[tuple[int, int], ...], int]:
    """Apply the checked fixed T2 or T4 spatial pullback to pair-half runs."""
    if type(steps) is not int or steps not in (2, 4):
        raise ValueError("punctured temporal action supports exactly T2 and T4")
    full_runs = _palindromic_runs(half_runs, odd=odd, work=work)
    result: tuple[tuple[int, int], ...] = ()
    width = 0
    for index in range(steps // 2):
        result, width = one_two_step_pair(full_runs, work)
        if index + 1 < steps // 2:
            full_runs = _palindromic_runs(result, odd=bool(width & 1), work=work)
    return result, width


__all__ = ["append_run", "punctured_pair_runs"]
