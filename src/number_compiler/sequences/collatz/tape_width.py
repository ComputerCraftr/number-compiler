"""Authenticated geometry-only width summaries for Collatz source actions."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys


@dataclass(frozen=True, slots=True)
class CollatzTapeWidthSummary:
    """Width and clock projection without source or endpoint integers.

    This is not a complete carry-tape result.  Producers publish it only when
    the selected source-bound action carries an exact width-spine summary.
    """

    source_width: int
    target_width: int
    physical_ticks: int
    normalized_symbols: int
    odd_steps: int
    blank: BlankLedger

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.source_width,
                self.target_width,
                self.physical_ticks,
                self.normalized_symbols,
                self.odd_steps,
            )
        ):
            raise TypeError("Collatz width summary fields require exact integers")
        if (
            self.source_width <= 0
            or self.target_width <= 0
            or self.physical_ticks < 0
            or self.normalized_symbols < 0
            or self.odd_steps < 0
        ):
            raise ValueError("Collatz width summary has a negative extent")
        if self.normalized_symbols + self.odd_steps != self.physical_ticks:
            raise ValueError("Collatz width summary clocks do not compose")
        if type(self.blank) is not BlankLedger:
            raise TypeError("Collatz width summary requires the canonical blank ledger")
        if self.blank.delta != self.target_width - self.source_width:
            raise ValueError("Collatz width summary lost its endpoint displacement")
        if (
            self.source_width + self.blank.minimum < 1
            or self.blank.minimum < -self.normalized_symbols
            or self.blank.maximum > 2 * self.odd_steps
        ):
            raise ValueError("Collatz width extrema exceed the physical-step bounds")


def compose_width_ledger(
    ledger: ResourceLedger, before: BlankLedger, after: BlankLedger
) -> BlankLedger:
    """Compose one derived segment and charge the arithmetic actually used."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("width-ledger composition requires its resource ledger")
    if type(before) is not BlankLedger or type(after) is not BlankLedger:
        raise TypeError("Collatz width composition requires canonical blank ledgers")
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TAPE_WIDTH_COMPOSITIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TAPE_WIDTH_OPERAND_BITS,
        sum(
            max(1, abs(value).bit_length())
            for value in (*before.as_tuple(), *after.as_tuple())
        ),
    )
    return before.then(after)


def cycle_width_summary(
    ledger: ResourceLedger, entry_phase: int, physical_ticks: int
) -> CollatzTapeWidthSummary:
    """Summarize a source-bound segment of the pinned three-state cycle."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("cycle width summary requires its resource ledger")
    if (
        type(entry_phase) is not int
        or not 0 <= entry_phase < 3
        or type(physical_ticks) is not int
        or physical_ticks < 0
    ):
        raise ValueError("invalid pinned-cycle width summary request")
    states = (1, 4, 2)
    cycle_ledgers = (
        BlankLedger(0, 0, 2),
        BlankLedger(0, -2, 0),
        BlankLedger(0, -1, 1),
    )
    cycles, remainder = divmod(physical_ticks, 3)
    cycle = cycle_ledgers[entry_phase]
    charge_width_repeat(ledger, cycle, cycles)
    result = cycle.repeat(cycles)
    odd_per_cycle = 1
    odd_tail = 0
    for offset in range(remainder):
        phase = (entry_phase + offset) % 3
        source = states[phase]
        target = states[(phase + 1) % 3]
        displacement = target.bit_length() - source.bit_length()
        segment = BlankLedger(
            displacement,
            min(0, displacement),
            max(0, displacement),
        )
        result = compose_width_ledger(ledger, result, segment)
        odd_tail += source & 1
    odd_steps = cycles * odd_per_cycle + odd_tail
    target_phase = (entry_phase + physical_ticks) % 3
    return CollatzTapeWidthSummary(
        states[entry_phase].bit_length(),
        states[target_phase].bit_length(),
        physical_ticks,
        physical_ticks - odd_steps,
        odd_steps,
        result,
    )


def charge_width_repeat(
    ledger: ResourceLedger, summary: BlankLedger, repeats: int
) -> None:
    """Charge the closed-form summary repeat without charging it as source work."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("width-ledger repeat requires its resource ledger")
    if type(summary) is not BlankLedger or type(repeats) is not int or repeats < 0:
        raise ValueError("invalid Collatz width summary repetition")
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TAPE_WIDTH_REPEAT_OPERATIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TAPE_WIDTH_OPERAND_BITS,
        max(1, repeats.bit_length())
        + sum(max(1, abs(value).bit_length()) for value in summary.as_tuple()),
    )


class CollatzWidthSpineAccumulator:
    """Track requested global and cache-segment width summaries together."""

    __slots__ = ("complete", "ledger", "requested", "segment", "total")

    def __init__(self, ledger: ResourceLedger, *, requested: bool) -> None:
        if type(ledger) is not ResourceLedger or type(requested) is not bool:
            raise TypeError(
                "Collatz width accumulator needs a ledger and Boolean demand"
            )
        self.ledger = ledger
        self.requested = requested
        self.complete = requested
        self.total = BlankLedger()
        self.segment = BlankLedger()

    def record(self, piece: BlankLedger) -> None:
        if not self.complete:
            return
        self.total = compose_width_ledger(self.ledger, self.total, piece)
        self.segment = compose_width_ledger(self.ledger, self.segment, piece)

    def invalidate(self) -> None:
        self.complete = False

    def segment_summary(
        self,
        source_width: int,
        target_width: int,
        normalized_symbols: int,
        odd_steps: int,
    ) -> CollatzTapeWidthSummary | None:
        if not self.complete or normalized_symbols <= 0:
            return None
        return CollatzTapeWidthSummary(
            source_width,
            target_width,
            normalized_symbols + odd_steps,
            normalized_symbols,
            odd_steps,
            self.segment,
        )

    def reset_segment(self) -> None:
        self.segment = BlankLedger()

    def finish(
        self,
        source_width: int,
        target_width: int,
        physical_ticks: int,
        normalized_symbols: int,
        odd_steps: int,
    ) -> CollatzTapeWidthSummary | None:
        if not self.complete:
            return None
        return CollatzTapeWidthSummary(
            source_width,
            target_width,
            physical_ticks,
            normalized_symbols,
            odd_steps,
            self.total,
        )


__all__ = ["CollatzTapeWidthSummary", "CollatzWidthSpineAccumulator"]
