"""Finite decimal pair transitions used by the Q19 image owner.

The operation includes the authenticated exact T2 group-ring/carry pullback and
bounded finite source-issued actions through T8192 without materializing
intermediate Q19 output occurrences. It consumes and returns maximal run tapes;
the caller owns source authority, ledger reservations, occurrence publication,
and larger temporal composition. This module deliberately contains no global
memo and makes no all-depth right-congruence or logarithmic future-power claim.
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
from number_compiler.arithmetic.fields.run_pairing import (
    append_run,
    pair_mirror_digit_runs,
)

from .reverse_group_ring import ReverseAddGroupRingCarry
from .temporal_port_quotient import (
    MAX_EXACT_DECIMAL_BLOCK_WIDTH,
    SymmetricCoefficientPort,
    native_decimal_string_transport,
)

MAX_PUNCTURED_TEMPORAL_STEPS = 8192


@dataclass(slots=True)
class PuncturedTemporalWork:
    """Actual run-record work performed by one bounded temporal pullback."""

    run_records_visited: int = 0
    prefix_queries: int = 0
    event_regions: int = 0
    output_runs: int = 0
    two_step_actions: int = 0
    half_tape_tick_transitions: int = 0
    native_decimal_ticks: int = 0
    native_decimal_digit_visits: int = 0
    spatial_projector_steps: int = 0
    spatial_projector_sections: int = 0


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

    def project_offsets(
        self,
        *,
        carries: Sequence[int] = (),
        symbols: Sequence[int] = (),
    ) -> tuple[dict[int, int], dict[int, int]]:
        """Project all demanded carry/symbol ports in one ordered run sweep.

        These are source-to-port projections, not per-occurrence memo IDs.
        Each half of the reflected group-ring stencil uses exactly the same
        complete carry prefix and therefore must not re-bisect its run tape.
        """
        requested_carries = sorted(set(carries))
        requested_symbols = sorted(set(symbols))
        if any(
            type(p) is not int or not 0 <= p <= self.width for p in requested_carries
        ):
            raise IndexError("carry projection outside Q19 width")
        if any(
            type(p) is not int or not 0 <= p < self.width for p in requested_symbols
        ):
            raise IndexError("symbol projection outside Q19 width")
        result_c: dict[int, int] = {}
        result_s: dict[int, int] = {}
        ci = 0
        for offset in requested_carries:
            if offset == 0:
                result_c[offset] = 0
                continue
            while self.ends[ci] < offset:
                ci += 1
            result_c[offset] = apply_carry_fn(self.effects[ci + 1], 0)
        si = 0
        for offset in requested_symbols:
            while self.ends[si] <= offset:
                si += 1
            result_s[offset] = self.runs[si][0]
        self.work.prefix_queries += len(requested_carries) + len(requested_symbols)
        self.work.run_records_visited += ci + si
        return result_c, result_s

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
    work.two_step_actions += 1
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

    # The production T2 coefficient map is the (I+R_W)(z-10)H correction.
    # The same group-ring action handles width births and reflected carry
    # endpoints, so the two orientations can never acquire separate drivers.
    group_ring = ReverseAddGroupRingCarry(width, ingress)
    if group_ring.next_raw_width != first_width:
        raise AssertionError("group-ring width skew disagrees with Q19")

    # Build the exact semantic port requests before evaluating the stencil.
    # A single sorted sweep resolves the low and reflected carry offsets.
    # Preserve the singleton scalar path for tiny words / external point-port
    # instrumentation: it does not pay for an unnecessary bulk table.
    sampled = {p for start, end in pairwise(ordered) for p in (start, end - 1)}
    if len(sampled) > 2:
        symbol_positions: set[int] = set()
        carry_positions: set[int] = set()
        for pos in sampled:
            symbol_positions.update(group_ring.symbol_offsets(pos))
            carry_positions.update(group_ring.carry_offsets(pos))
        carry_values, symbol_values = source.project_offsets(
            carries=tuple(carry_positions), symbols=tuple(symbol_positions)
        )

        def coefficient(index: int) -> int:
            return group_ring.coefficient(
                index,
                symbol_at=symbol_values.__getitem__,
                carry_at=carry_values.__getitem__,
            )
    else:

        def coefficient(index: int) -> int:
            return group_ring.coefficient(
                index, symbol_at=source.symbol_at, carry_at=source.carry_at
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


def _bounded_native_group_ring_block(
    state: SymmetricCoefficientPort,
    steps: int,
    work: PuncturedTemporalWork,
) -> SymmetricCoefficientPort:
    """Run a bounded exact decimal block from one symmetric pair source.

    The Q19 pair field is normalized once by its exact group-ring/carry law.
    The remaining physical transitions use exact bounded decimal strings, and
    only the final symmetric half-tape is returned for owner publication.
    This does not predict future carry words or authorize an unvisited period.
    """
    normalized, carry, visits = state.normalize_with_carry()
    work.run_records_visited += visits + len(normalized)
    work.half_tape_tick_transitions += 1
    text = "".join(str(digit) * length for digit, length in reversed(normalized))
    if len(text) != carry.target_width or (len(text) > 1 and text[0] == "0"):
        raise AssertionError("group-ring normalization lost its exact decimal seam")
    work.native_decimal_digit_visits += len(text)
    before_tick_visits = work.native_decimal_digit_visits

    def record_started_tick(input_width: int) -> None:
        work.native_decimal_ticks += 1
        work.native_decimal_digit_visits += input_width

    final_text, tick_visits = native_decimal_string_transport(
        text,
        steps - 1,
        on_tick_start=record_started_tick,
    )
    work.native_decimal_digit_visits += len(final_text)
    if tick_visits != work.native_decimal_digit_visits - before_tick_visits:
        raise AssertionError("native decimal digit-work accounting diverged")

    width = len(final_text)
    encoded = final_text.encode("ascii")
    half: list[tuple[int, int]] = []
    for index in range((width + 1) // 2):
        pair = encoded[index] + encoded[width - index - 1] - 96
        append_run(half, pair, 1)
    work.run_records_visited += 2 * len(half)
    work.output_runs += len(half)
    work.two_step_actions += steps // 2
    return SymmetricCoefficientPort(width, tuple(half))


def punctured_pair_runs(
    half_runs: Sequence[tuple[int, int]],
    *,
    odd: bool,
    steps: int,
    work: PuncturedTemporalWork,
) -> tuple[tuple[tuple[int, int], ...], int]:
    """Compose one bounded exact source action and return its endpoint tape.

    Each primitive tick uses the exact normalized-digit and symmetric
    half-tape successor, or the bounded native decimal route after one exact
    group-ring normalization. No intermediate Q19 occurrence is issued and no
    periodic continuation is assumed. Durations 16 through the configured
    finite maximum are accepted as chronological actions, including odd and
    non-dyadic spans.
    """
    if type(steps) is not int or not (
        steps in (2, 4) or 16 <= steps <= MAX_PUNCTURED_TEMPORAL_STEPS
    ):
        raise ValueError("punctured temporal action exceeds its finite bound")
    state = SymmetricCoefficientPort.from_half_runs(half_runs, odd=odd)
    work.run_records_visited += 3 * len(state.half_runs)
    if steps >= 16 and state.width + steps <= MAX_EXACT_DECIMAL_BLOCK_WIDTH:
        target = _bounded_native_group_ring_block(state, steps, work)
        return target.half_runs, target.width
    for tick in range(steps):
        transition = state.successor_with_carry()
        state = transition.target
        work.half_tape_tick_transitions += 1
        work.run_records_visited += transition.run_records_visited
        work.output_runs += len(state.half_runs)
        if tick & 1:
            work.two_step_actions += 1
    return state.half_runs, state.width


__all__ = ["append_run", "punctured_pair_runs"]
