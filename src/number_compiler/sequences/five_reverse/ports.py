"""Source-bound finite port observations for the five-reversal recurrence."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedPhaseCoordinate,
    OrderedSourceCoverage,
)

MAX_FIVE_REVERSE_MATRIX_STEPS = 4096
MAX_FIVE_REVERSE_TRACE_STEPS = 128


@dataclass(frozen=True, slots=True)
class FiveBorderPort:
    """Exact bounded view of one physical value, without execution authority."""

    decimal_width: int
    high_digits: tuple[int, ...]
    low_digits: tuple[int, ...]
    residue45: int


@dataclass(frozen=True, slots=True)
class FiveCarryPort:
    """Exact carry and parity projections of one certified border state."""

    stage: int
    head3: int
    tail3: int
    carry_mod25: int
    carry_mod125: int
    source_parity: int
    opposite_parity: int
    width_growth: int | None


@dataclass(frozen=True, slots=True)
class FivePortTransition:
    """One exact adjacent source/target port pair in a finite window."""

    physical_tick: int
    source: FiveBorderPort | FiveCarryPort
    target: FiveBorderPort | FiveCarryPort


@dataclass(frozen=True, slots=True)
class FiveSourceTransfer:
    """Finite port observation selected by one source-bound term.

    The phase fields are source residues modulo 45. They are separate from the
    certified finite window's ``stage`` coordinate on ``FiveCarryPort``.
    """

    source_index: int
    steps: int
    start_phase: int
    terminal_phase: int
    initial_port: FiveBorderPort | FiveCarryPort
    terminal_port: FiveBorderPort | FiveCarryPort
    trace: tuple[FivePortTransition, ...]
    source_coverage: OrderedSourceCoverage = OrderedSourceCoverage.EXACT_BOUNDED_WINDOW
    phase_coordinate: OrderedPhaseCoordinate = field(
        default=OrderedPhaseCoordinate.SOURCE_MOD45, init=False
    )
    clock_unit: Literal["physical-recurrence-ticks"] = field(
        default="physical-recurrence-ticks", init=False
    )
    law: Literal["five-reversal-exact-port-transition"] = field(
        default="five-reversal-exact-port-transition", init=False
    )
    authority_scope: Literal["finite-port-transfer"] = field(
        default="finite-port-transfer", init=False
    )
    physical_repeat_certified: bool = False
    future_repetition_claimed: bool = False
    execution_authority: bool = False

    def pascal_innovation(self) -> tuple[int, ...] | None:
        """Read the four finite F5 coefficients from the admitted carry rows."""
        if self.source_coverage is not OrderedSourceCoverage.FIVE_GUARDED_WINDOW:
            return None
        if len(self.trace) != 4:
            return None
        row: list[int] = []
        for transition in self.trace:
            source = transition.source
            if not isinstance(source, FiveCarryPort) or source.carry_mod25 != 11:
                raise ValueError("guarded carry row lost its mod-25 parent")
            row.append((source.carry_mod125 - 11) // 25)
        coefficients: list[int] = []
        while row:
            coefficients.append(row[0])
            row = [
                (right - left) % 5
                for left, right in zip(row[:-1], row[1:], strict=True)
            ]
        return tuple(coefficients)

    def __post_init__(self) -> None:
        require_integer(self.source_index, "five-reversal source index", 0)
        require_integer(self.steps, "five-reversal physical ticks", 0)
        require_integer(self.start_phase, "five-reversal start phase", 0, 44)
        require_integer(self.terminal_phase, "five-reversal terminal phase", 0, 44)
        if type(self.source_coverage) is not OrderedSourceCoverage or (
            self.source_coverage
            not in (
                OrderedSourceCoverage.EXACT_BOUNDED_WINDOW,
                OrderedSourceCoverage.FIVE_GUARDED_WINDOW,
            )
        ):
            raise TypeError("five-reversal transfer needs a declared finite coverage")
        if type(self.initial_port) not in (FiveBorderPort, FiveCarryPort) or (
            type(self.terminal_port) not in (FiveBorderPort, FiveCarryPort)
        ):
            raise TypeError("five-reversal transfer ports have a foreign owner")
        if type(self.trace) is not tuple or any(
            type(transition) is not FivePortTransition for transition in self.trace
        ):
            raise TypeError(
                "five-reversal transfer trace must be an immutable port tuple"
            )
        if self.trace and len(self.trace) != self.steps:
            raise ValueError("five-reversal trace must cover its physical horizon")
        if any(
            transition.physical_tick != self.source_index + offset
            for offset, transition in enumerate(self.trace)
        ):
            raise ValueError("five-reversal trace has a mismatched source clock")
        if self.physical_repeat_certified or self.future_repetition_claimed:
            raise ValueError("finite five-reversal windows cannot claim repetition")
        if self.execution_authority:
            raise ValueError(
                "five-reversal transfer packets carry no execution authority"
            )


def source_residue45(seed: int, generation: int) -> int:
    """Exact 5*reverse10 residue clock, independent of carry-path claims."""

    seed = require_integer(seed, "five-reversal seed", 0)
    generation = require_integer(generation, "five-reversal generation", 0)
    if generation == 0:
        return seed % 45
    return (10 * (seed * pow(5, generation, 9) % 9)) % 45
