"""Detached ordered-band measurements, carrying no execution authority.

`source_index` and `physical_ticks` identify a finite source window. Optional
phase values are present only when a family declares the matching coordinate.
"""

from dataclasses import dataclass, field
from enum import StrEnum

from number_compiler.arithmetic.fields.ordered_matrix import Matrix2, OrderedCovector


class OrderedBandChannel(StrEnum):
    LOWER_CARRY = "lower-carry"
    UPPER_CARRY = "upper-carry"
    SOURCE_PARITY = "source-parity"
    OPPOSITE_PARITY = "opposite-parity"
    LOWER_DIGITS = "lower-digits"
    UPPER_DIGITS = "upper-digits"
    SOURCE_DIGITS = "source-digits"


class OrderedSourceCoverage(StrEnum):
    SCHEDULER_WINDOW = "exact-scheduler-issued-physical-window"
    Q19_CHILD_PATH = "exact-issued-q19-child-path"
    FIVE_GUARDED_WINDOW = "guarded-four-stage-source-window"
    EXACT_BOUNDED_WINDOW = "exact-bounded-recurrence-window"


class OrderedPhaseCoordinate(StrEnum):
    NONE = "none"
    SOURCE_MOD45 = "source-mod45"


@dataclass(frozen=True, slots=True)
class OrderedBandOutput:
    source_index: int
    physical_ticks: int
    start_phase: int | None
    terminal_phase: int | None
    channels: tuple[OrderedBandChannel, ...]
    matrices: tuple[Matrix2, ...]
    covectors: tuple[OrderedCovector, ...]
    source_coverage: OrderedSourceCoverage
    matrix_multiplications: int
    source_letters_read: int
    trace: tuple[tuple[Matrix2, ...], ...] = ()
    phase_coordinate: OrderedPhaseCoordinate = OrderedPhaseCoordinate.NONE
    execution_authority: bool = field(default=False, init=False)

    def __post_init__(self) -> None:
        if type(self.source_index) is not int or self.source_index < 0:
            raise ValueError("ordered source index must be a nonnegative exact integer")
        if type(self.physical_ticks) is not int or self.physical_ticks < 1:
            raise ValueError("ordered physical ticks must be positive exact integers")
        if type(self.source_coverage) is not OrderedSourceCoverage:
            raise TypeError("ordered source coverage must use a declared finite owner")
        if type(self.phase_coordinate) is not OrderedPhaseCoordinate:
            raise TypeError("ordered phase coordinates require a declared clock")
        if self.phase_coordinate is OrderedPhaseCoordinate.NONE:
            if self.start_phase is not None or self.terminal_phase is not None:
                raise ValueError("finite windows without a phase clock use null phases")
        elif self.phase_coordinate is OrderedPhaseCoordinate.SOURCE_MOD45:
            if (
                type(self.start_phase) is not int
                or type(self.terminal_phase) is not int
                or not 0 <= self.start_phase < 45
                or not 0 <= self.terminal_phase < 45
            ):
                raise ValueError("mod-45 phase coordinates must be residues 0..44")
        if (
            type(self.matrix_multiplications) is not int
            or self.matrix_multiplications < 0
        ):
            raise ValueError("ordered matrix work must be a nonnegative exact count")
        if type(self.source_letters_read) is not int or self.source_letters_read < 0:
            raise ValueError("ordered source reads must be a nonnegative exact count")
        if len(self.channels) != len(self.matrices) or (
            self.covectors and len(self.covectors) != len(self.matrices)
        ):
            raise ValueError("ordered output channels differ from emitted matrices")
        if self.trace and (
            len(self.trace) != self.physical_ticks
            or any(len(row) != len(self.channels) for row in self.trace)
        ):
            raise ValueError("ordered trace must cover every physical tick and channel")
