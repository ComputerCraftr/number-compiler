"""Streaming composition of explicit radix-64 accelerated Collatz events.

Each event derives carry from five-way geometry and retains separate bounded
directional value views across its one-cell lookahead. Only final digits are
collected. This is finite streaming execution, not logarithmic temporal
powering or a certificate for a minimized universal controller.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.carry.collatz_output_quotient import (
    radix64_geometry_emit,
    radix64_growth_edge,
    radix64_join_shift_views,
    radix64_shift_views,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.two_adic import v2_positive


class Radix64CollatzStage:
    """Transient controller, value register and external valuation geometry.

    No stage instance is a semantic class ID or a cache key. ``stripped`` and
    ``source_width`` are exact geometry; ``pending`` is one left value view.
    """

    __slots__ = (
        "stripped",
        "shift",
        "carry",
        "carry_peak",
        "pending",
        "source_width",
        "last_nonzero",
        "closed",
    )

    def __init__(self) -> None:
        self.stripped = 0
        self.shift: int | None = None
        self.carry = 1
        self.carry_peak = 0
        self.pending: int | None = None
        self.source_width = 0
        self.last_nonzero = False
        self.closed = False

    @property
    def valuation(self) -> int:
        if not self.closed:
            raise ValueError("valuation requires a finalized source boundary")
        return 6 * self.stripped + (self.shift or 0)

    def feed(self, digit: int) -> int | None:
        if self.closed:
            raise ValueError("cannot feed a finalized Collatz stage")
        outgoing, raw = radix64_geometry_emit(digit, self.carry)
        if self.source_width == 0 and not digit & 1:
            raise ValueError("accelerated Collatz source must be odd")
        self.source_width += 1
        self.last_nonzero = digit != 0
        if self.shift is None:
            if digit == 21:
                self.stripped += 1
                return None
            self.shift = v2_positive(3 * digit + 1)
            if self.shift >= 6:
                raise AssertionError("uncropped sentinel reached the raw controller")
        self.carry = outgoing
        self.carry_peak = max(self.carry_peak, self.carry)
        quotient, remainder = radix64_shift_views(raw, self.shift)
        previous, self.pending = self.pending, quotient
        if previous is None:
            return None
        return radix64_join_shift_views(previous, remainder, self.shift)

    def finish(self) -> tuple[int, ...]:
        if self.closed:
            raise ValueError("Collatz stage was already finalized")
        if not self.source_width or not self.last_nonzero:
            raise ValueError("source requires a nonempty canonical radix-64 word")
        self.closed = True
        if self.pending is None:
            # An all-sentinel source has 3*n+1 = 64**q.
            return (1,)
        if self.shift is None:
            raise AssertionError("raw output lost its residual phase")
        _, remainder = radix64_shift_views(self.carry, self.shift)
        last = radix64_join_shift_views(self.pending, remainder, self.shift)
        edge = radix64_growth_edge(self.carry, self.shift)
        if edge:
            return last, edge
        # Division by at most 32 removes at most one radix-64 source digit.
        # If this last digit is zero, the preceding emitted digit is nonzero.
        return (last,) if last else ()


@dataclass(frozen=True, slots=True)
class Radix64TemporalResult:
    """An explicitly requested endpoint, never retained as a lazy summary."""

    target_digits: tuple[int, ...]
    valuation: int
    source_frame: int
    source_shift: int
    exit_frame: int
    carry_peak: int


def _push(
    stages: Sequence[Radix64CollatzStage], start: int, digit: int, output: list[int]
) -> None:
    for i in range(start, len(stages)):
        emitted = stages[i].feed(digit)
        if emitted is None:
            return
        digit = emitted
    output.append(digit)


def compose_radix64_events(
    digits: Iterable[int], events: int = 1, *, max_events: int = 64
) -> Radix64TemporalResult:
    """Compose finite streaming events with no intermediate digit collections.

    The event cap bounds the transient pipeline before reading the source.
    Exact accumulated valuation and exit frame are output metadata, not
    controller identity. Work can still grow linearly with event count.
    """
    if type(events) is not int or type(max_events) is not int:
        raise TypeError("event counts require exact integers")
    if events < 1 or max_events < 1:
        raise ValueError("event counts must be positive")
    if events > max_events:
        raise BlockContextBudgetExceeded("radix-64 streaming event budget exceeded")
    stages = [Radix64CollatzStage() for _ in range(events)]
    output: list[int] = []
    for digit in digits:
        _push(stages, 0, digit, output)
    for i, stage in enumerate(stages):
        for digit in stage.finish():
            _push(stages, i + 1, digit, output)
    frame = 0
    for digit in output:
        if digit != 21:
            break
        frame += 1
    return Radix64TemporalResult(
        tuple(output),
        sum(stage.valuation for stage in stages),
        stages[0].stripped,
        stages[0].shift or 0,
        frame,
        max(stage.carry_peak for stage in stages),
    )
