"""Exact decimal reverse/add width from successor carry rows.

The cursor and its bounded carry suffix are temporary compiler state.  The
published value is only a scalar ``BlankLedger`` summary, so a width query does
not manufacture a completed output occurrence.
"""

from __future__ import annotations

import traceback
from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_itinerary import (
    live_event_suffix_start,
    reconstruct_pair_from_live_event_suffix,
)
from number_compiler.arithmetic.carry.event_memory import (
    _pair_step_with_carry,
    carry_field,
    event_memory_horizon,
    forcing_event_from_carry,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class ReverseSuccessorWidthSummary:
    """Exact scalar width projection retained by the source projection cache."""

    steps: int
    source_width: int
    blank: BlankLedger

    def __post_init__(self) -> None:
        if type(self.steps) is not int or self.steps < 0:
            raise ValueError("successor width steps must be nonnegative")
        if type(self.source_width) is not int or self.source_width < 1:
            raise ValueError("successor width needs a positive source width")
        if type(self.blank) is not BlankLedger:
            raise TypeError("successor width requires the shared blank ledger")
        if not 0 <= self.blank.delta <= self.steps:
            raise ValueError("successor width has an invalid growth total")
        if self.blank.minimum != 0 or self.blank.maximum != self.blank.delta:
            raise ValueError("reverse/add width growth must be monotone")

    @property
    def target_width(self) -> int:
        return self.source_width + self.blank.delta


def _bump_peak(ledger: ResourceLedger, name: str, value: int) -> None:
    previous = ledger.counters.get(name, 0)
    if value > previous:
        ledger.bump(name, value - previous)


def _record_reconstruction_work(ledger: ResourceLedger, updates: int) -> None:
    """Record completed coefficient updates, including a failed reconstruction."""
    ledger.bump("reverse_successor_tape_reconstruction_coefficient_updates", updates)
    ledger.bump("reverse_successor_tape_reconstruction_multiply_terms", 2 * updates)
    ledger.bump("reverse_successor_tape_reconstruction_add_terms", updates)
    ledger.bump("reverse_successor_tape_reconstruction_reduction_terms", updates)


def _reconstruct_live(
    ledger: ResourceLedger,
    events: tuple[tuple[int, ...], ...],
    *,
    lane: str,
) -> tuple[int, ...]:
    ledger.bump(f"reverse_successor_tape_{lane}_reconstructions")
    return reconstruct_pair_from_live_event_suffix(
        events,
        base=10,
        record_updates=lambda updates: _record_reconstruction_work(ledger, updates),
    )


def compile_reverse_successor_width(
    digits_lsd: tuple[int, ...],
    steps: int,
    *,
    ledger: ResourceLedger,
    scratch_owner: int | None,
) -> ReverseSuccessorWidthSummary:
    """Compile exact width from the successor carry/borrow recurrence.

    The first event-memory horizon is bootstrapped from the original symmetric
    pair. At the H-row cutover, one live-event reconstruction must match the
    directly stepped endpoint. Later endpoints come from the retained live
    event suffix. The cursor retains event tuples rather than carry history;
    the returned summary retains no row, pair, target root, or digit word. This
    sequential compiler remains a reference path, not a powered transducer.
    """
    if type(ledger) is not ResourceLedger:
        raise TypeError("successor width requires its source ledger")
    for counter in (
        "reverse_successor_tape_rows",
        "reverse_successor_tape_bootstrap_rows",
        "reverse_successor_tape_spatial_bits",
        "reverse_successor_tape_pair_operand_symbols",
        "reverse_successor_tape_event_symbols",
        "reverse_successor_tape_vector_cutovers",
        "reverse_successor_tape_live_rows_peak",
        "reverse_successor_tape_cutover_reconstructions",
        "reverse_successor_tape_live_reconstructions",
        "reverse_successor_tape_reconstruction_coefficient_updates",
        "reverse_successor_tape_reconstruction_multiply_terms",
        "reverse_successor_tape_reconstruction_add_terms",
        "reverse_successor_tape_reconstruction_reduction_terms",
        "reverse_successor_tape_width_failures",
    ):
        ledger.bump(counter, 0)
    if type(digits_lsd) is not tuple or not digits_lsd:
        raise ValueError("successor width requires canonical source digits")
    if type(steps) is not int or steps < 0:
        raise ValueError("successor width steps must be nonnegative")
    if any(type(digit) is not int or not 0 <= digit <= 9 for digit in digits_lsd):
        raise ValueError("successor width requires decimal source digits")
    if len(digits_lsd) > 1 and digits_lsd[-1] == 0:
        raise ValueError("successor width requires canonical source width")

    source_width = len(digits_lsd)
    if digits_lsd == (0,):
        ledger.bump("reverse_successor_tape_fixed_point_hits")
        ledger.bump("reverse_successor_tape_width_compilations")
        return ReverseSuccessorWidthSummary(steps, source_width, BlankLedger())
    if steps == 0:
        ledger.bump("reverse_successor_tape_width_compilations")
        return ReverseSuccessorWidthSummary(steps, source_width, BlankLedger())
    if scratch_owner is None:
        raise ValueError("nonzero successor width needs a scratch owner")

    base = 10
    horizon = event_memory_horizon(base)
    history: Sequence[tuple[int, ...]] = ()
    seed_events: list[tuple[int, ...]] = []
    live_events: tuple[tuple[int, ...], ...] = ()
    pending_pair: tuple[int, ...] | None = None
    pair: tuple[int, ...] = ()
    current_pair: tuple[int, ...] = ()
    next_pair: tuple[int, ...] | None = None
    carry: tuple[int, ...] = ()
    event: tuple[int, ...] = ()
    expanded_events: tuple[tuple[int, ...], ...] = ()
    reconstructed_pair: tuple[int, ...] = ()
    total_growth = 0
    scratch_nodes = 0
    live_peak = 0
    try:
        ledger.reserve(scratch_owner, nodes=source_width)
        scratch_nodes = source_width
        pair = tuple(
            digits_lsd[index] + digits_lsd[source_width - 1 - index]
            for index in range(source_width)
        )
        for index in range(steps):
            live_mode = bool(live_events)
            history = live_events if live_mode else seed_events
            history_bits = sum(map(len, history))
            history_rows = len(history)
            width = (
                len(pending_pair)
                if pending_pair is not None
                else len(pair)
                if not live_mode
                else len(live_events[-1])
            )
            # Covers the bounded event suffix, reconstruction copies, endpoint
            # and carry vectors, and cutover temporaries before allocation.
            work_nodes = 4 * history_bits + 12 * (width + 1) + 4 * history_rows
            ledger.reserve(scratch_owner, nodes=work_nodes)
            scratch_nodes += work_nodes
            next_pair = None
            event = ()
            expanded_events = ()
            reconstructed_pair = ()
            if not live_mode:
                current_pair = pair
                needs_next_pair = index + 1 < steps
                if needs_next_pair:
                    next_pair, growth, carry = _pair_step_with_carry(current_pair, base)
                else:
                    carry = carry_field(current_pair, base=base)
                    growth = carry[-1]
                ledger.bump("reverse_successor_tape_bootstrap_rows")
            else:
                if pending_pair is not None:
                    # Reuse the cutover endpoint as the first live input; this
                    # avoids reconstructing that same pair a second time.
                    current_pair = pending_pair
                    pending_pair = None
                else:
                    current_pair = _reconstruct_live(ledger, live_events, lane="live")
                carry = carry_field(current_pair, base=base)
                growth = carry[-1]
            total_growth += growth
            ledger.bump("reverse_successor_tape_rows")
            ledger.bump("reverse_successor_tape_spatial_bits", len(current_pair))
            ledger.bump(
                "reverse_successor_tape_pair_operand_symbols",
                len(current_pair),
            )

            needs_next_row = index + 1 < steps
            if not live_mode:
                if needs_next_row and steps > horizon:
                    event = forcing_event_from_carry(carry, base=base)
                    ledger.bump("reverse_successor_tape_event_symbols", len(event))
                    seed_events.append(event)
                if len(seed_events) == horizon and needs_next_row:
                    start = live_event_suffix_start(seed_events, base=base)
                    live_events = tuple(seed_events[start:])
                    reconstructed_pair = _reconstruct_live(
                        ledger, live_events, lane="cutover"
                    )
                    if reconstructed_pair != next_pair:
                        raise AssertionError(
                            "successor carry cutover lost its endpoint pair"
                        )
                    pending_pair = reconstructed_pair
                    # Bootstrap temporarily retains all H event rows, then
                    # transfers only the proved live suffix to its cursor.
                    live_peak = max(live_peak, len(seed_events))
                    seed_events.clear()
                    pair = ()
                    ledger.bump("reverse_successor_tape_vector_cutovers")
                else:
                    pair = next_pair if next_pair is not None else ()
            else:
                if needs_next_row:
                    event = forcing_event_from_carry(carry, base=base)
                    ledger.bump("reverse_successor_tape_event_symbols", len(event))
                    expanded_events = live_events + (event,)
                    start = live_event_suffix_start(expanded_events, base=base)
                    live_events = expanded_events[start:]
                    live_peak = max(live_peak, len(live_events))

            current_pair = ()
            carry = ()
            next_pair = None
            event = ()
            expanded_events = ()
            reconstructed_pair = ()
            history = ()
            retained_nodes = len(pair) + sum(map(len, seed_events))
            retained_nodes += sum(map(len, live_events))
            if pending_pair is not None:
                retained_nodes += len(pending_pair)
            if scratch_nodes > retained_nodes:
                ledger.release(scratch_owner, nodes=scratch_nodes - retained_nodes)
                scratch_nodes = retained_nodes
            elif retained_nodes > scratch_nodes:
                ledger.reserve(scratch_owner, nodes=retained_nodes - scratch_nodes)
                scratch_nodes = retained_nodes

        _bump_peak(ledger, "reverse_successor_tape_live_rows_peak", live_peak)
        ledger.bump("reverse_successor_tape_width_compilations")
        return ReverseSuccessorWidthSummary(
            steps, source_width, BlankLedger(total_growth, 0, total_growth)
        )
    except BaseException as error:
        ledger.bump("reverse_successor_tape_width_failures")
        traceback.clear_frames(error.__traceback__)
        raise
    finally:
        del (
            pair,
            seed_events,
            live_events,
            history,
            pending_pair,
            current_pair,
            next_pair,
            carry,
            event,
            expanded_events,
            reconstructed_pair,
        )
        if scratch_nodes:
            ledger.release(scratch_owner, nodes=scratch_nodes)


__all__ = ["ReverseSuccessorWidthSummary", "compile_reverse_successor_width"]
