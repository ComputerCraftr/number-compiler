"""Typed identities for guarded Collatz border actions.

Cycle identity and entry phase are semantic. Their display labels are derived
metadata and are never parsed back into an action selector.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, TypeGuard

CLOSED_BORDER_CYCLE_TAG: Final[str] = "collatz-closed-border-cycle-v1"
GUARDED_BORDER_PATH_TAG: Final[str] = "collatz-guarded-border-path-v1"


@dataclass(frozen=True, slots=True)
class ClosedBorderCycle:
    """A digit cycle stored in its least rotational form (without reflection)."""

    digits: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.digits) is not tuple
            or len(self.digits) < 2
            or any(
                type(digit) is not int or not 0 <= digit <= 9 for digit in self.digits
            )
        ):
            raise ValueError("border cycle must contain at least two decimal digits")
        if len(set(self.digits)) != len(self.digits):
            raise ValueError("border cycle digits must identify every phase uniquely")
        rotations = tuple(
            self.digits[index:] + self.digits[:index]
            for index in range(len(self.digits))
        )
        if self.digits != min(rotations):
            raise ValueError("border cycle must use its least rotational form")

    @classmethod
    def from_rotation(cls, digits: tuple[int, ...]) -> ClosedBorderCycle:
        if type(digits) is not tuple or len(digits) < 2:
            raise ValueError("border cycle requires a digit tuple")
        rotations = tuple(
            digits[index:] + digits[:index] for index in range(len(digits))
        )
        return cls(min(rotations))

    def phase_for_entry(self, entry_digit: int) -> int:
        if type(entry_digit) is not int or entry_digit not in self.digits:
            raise ValueError("cycle entry digit is not on this cycle")
        return self.digits.index(entry_digit)

    def structural_key(self, phase: int) -> tuple[object, ...]:
        """Encode this canonical cycle occurrence for immutable image ports."""
        if type(phase) is not int or not 0 <= phase < len(self.digits):
            raise ValueError("cycle structural key has an invalid entry phase")
        return (CLOSED_BORDER_CYCLE_TAG, self.digits, phase)


@dataclass(frozen=True, slots=True)
class CycleEntryPhase:
    """One admitted occurrence orientation of a closed border cycle."""

    cycle: ClosedBorderCycle
    phase: int

    def __post_init__(self) -> None:
        if type(self.cycle) is not ClosedBorderCycle:
            raise TypeError("cycle occurrence requires a canonical closed cycle")
        if type(self.phase) is not int or not 0 <= self.phase < len(self.cycle.digits):
            raise ValueError("cycle entry phase is outside the cycle")

    @property
    def entry_digit(self) -> int:
        return self.cycle.digits[self.phase]

    @property
    def display_label(self) -> str:
        digits = self.cycle.digits
        rotated = digits[self.phase :] + digits[: self.phase]
        return "".join(map(str, (*rotated, rotated[0])))

    def observation(self, *, run_parameters: tuple[int, ...] = ()) -> dict[str, object]:
        return {
            "kind": "closed-cycle",
            "cycle": self.cycle.digits,
            "entry_phase": self.phase,
            "entry_digit": self.entry_digit,
            "run_parameters": run_parameters,
            "display_label": self.display_label,
        }

    def structural_key(self) -> tuple[object, ...]:
        """Encode typed phase without relying on enum or display objects."""
        return self.cycle.structural_key(self.phase)


class BoundaryPathKind(Enum):
    """Guarded open or variable-tail border programs."""

    SIX_THREE_ZERO = "six-three-zero"
    THREE_ZERO_FIVE = "three-zero-five"
    THREE_BORDER_RETURN = "three-border-return"


class BorderEntryPort(Enum):
    DIGIT_ZERO = 0
    DIGIT_THREE = 3
    DIGIT_FIVE = 5
    DIGIT_SIX = 6


class BorderExitPort(Enum):
    UNRESOLVED = "unresolved"
    RETURN_TO_THREE = "return_to_3"
    RETURN_AT_HORIZON = "return_at_horizon"
    EIGHT_TO_FOUR = "8_to_4"
    EIGHT_TO_NINE = "8_to_9"
    EIGHT_TO_NINE_TO_EIGHT = "8_to_9_to_8"
    EIGHT_TO_NINE_OPEN = "8_to_9_open"
    EIGHT_TO_NINE_PENDING = "8_to_9_pending"


class NonBorderSegment(Enum):
    ZERO_RUN = "zero_run"
    TERMINAL_POWER_OF_TWO = "terminal"


@dataclass(frozen=True, slots=True)
class GuardedBorderPath:
    """A guarded path with explicit ports; run data stays on its occurrence."""

    kind: BoundaryPathKind
    entry_digit: int
    exit_digit: int | None

    def __post_init__(self) -> None:
        if type(self.kind) is not BoundaryPathKind:
            raise TypeError("guarded path requires a declared path kind")
        if type(self.entry_digit) is not int or not 0 <= self.entry_digit <= 9:
            raise ValueError("guarded path entry must be a decimal digit")
        if self.exit_digit is not None and (
            type(self.exit_digit) is not int or not 0 <= self.exit_digit <= 9
        ):
            raise ValueError("guarded path exit must be a decimal digit or absent")
        if self.kind is BoundaryPathKind.SIX_THREE_ZERO and (
            self.entry_digit != 6 or self.exit_digit != 0
        ):
            raise ValueError("6→3→0 path requires its exact entry and exit digits")
        if self.kind is BoundaryPathKind.THREE_ZERO_FIVE and (
            self.entry_digit != 3 or self.exit_digit != 5
        ):
            raise ValueError("3→0*→5 path requires its exact entry and exit digits")
        if self.kind is BoundaryPathKind.THREE_BORDER_RETURN and (
            self.entry_digit not in (0, 3, 5, 6) or self.exit_digit not in (3, 4, 8, 9)
        ):
            raise ValueError("border-return path has an unsupported entry or exit")

    @property
    def display_label(self) -> str:
        if self.kind is BoundaryPathKind.SIX_THREE_ZERO:
            return "6→3→0"
        if self.kind is BoundaryPathKind.THREE_ZERO_FIVE:
            return "3→0*→5"

        entry_prefix = {
            0: "0*→(3|5→6→3)→",
            3: "3→",
            5: "5→6→3→",
            6: "6→3→",
        }.get(self.entry_digit)
        if entry_prefix is None or self.exit_digit not in (3, 4, 8, 9):
            raise ValueError("border-return path has an unsupported entry or exit")
        exit_suffix = {
            3: "3",
            4: "8→4",
            8: "8",
            9: "8→9",
        }[self.exit_digit]
        return f"{entry_prefix}0*→5→6→{exit_suffix}"

    def observation(self, *, run_parameters: tuple[int, ...] = ()) -> dict[str, object]:
        return {
            "kind": "guarded-path",
            "path_kind": self.kind.value,
            "entry_digit": self.entry_digit,
            "exit_digit": self.exit_digit,
            "run_parameters": run_parameters,
            "display_label": self.display_label,
        }

    def structural_key(self) -> tuple[object, ...]:
        """Encode guarded path control and ports for immutable image ports."""
        return (
            GUARDED_BORDER_PATH_TAG,
            self.kind.value,
            self.entry_digit,
            self.exit_digit,
        )


BoundaryActionIdentity: TypeAlias = CycleEntryPhase | GuardedBorderPath
CollatzSegmentIdentity: TypeAlias = BoundaryActionIdentity | NonBorderSegment
BoundaryOccurrence: TypeAlias = tuple[int, int, int, BoundaryActionIdentity]


def is_boundary_occurrence(value: object) -> TypeGuard[BoundaryOccurrence]:
    """Validate the typed identity carried by one admitted border occurrence."""
    return (
        type(value) is tuple
        and len(value) == 4
        and type(value[0]) is int
        and value[0] >= 0
        and type(value[1]) is int
        and type(value[2]) is int
        and type(value[3]) in (CycleEntryPhase, GuardedBorderPath)
    )


def _cycle(digits: tuple[int, ...]) -> ClosedBorderCycle:
    return ClosedBorderCycle.from_rotation(digits)


CYCLE_421 = _cycle((4, 2, 1))
CYCLE_4721 = _cycle((4, 7, 2, 1))
CYCLE_0563 = _cycle((0, 5, 6, 3))
CYCLE_26847 = _cycle((2, 6, 8, 4, 7))
CYCLE_89 = _cycle((8, 9))

ENTRY_421 = CycleEntryPhase(CYCLE_421, CYCLE_421.phase_for_entry(4))
ENTRY_4721 = CycleEntryPhase(CYCLE_4721, CYCLE_4721.phase_for_entry(4))
ENTRY_0563 = CycleEntryPhase(CYCLE_0563, CYCLE_0563.phase_for_entry(0))
ENTRY_26847_PHASES = tuple(
    CycleEntryPhase(CYCLE_26847, phase) for phase in range(len(CYCLE_26847.digits))
)
ENTRY_89_AT_NINE = CycleEntryPhase(CYCLE_89, CYCLE_89.phase_for_entry(9))

PATH_630 = GuardedBorderPath(BoundaryPathKind.SIX_THREE_ZERO, 6, 0)
PATH_305 = GuardedBorderPath(BoundaryPathKind.THREE_ZERO_FIVE, 3, 5)


def cycle_phase(
    identity: BoundaryActionIdentity, cycle: ClosedBorderCycle
) -> int | None:
    if type(identity) is CycleEntryPhase and identity.cycle == cycle:
        return identity.phase
    return None


def border_return_path(entry_digit: int, exit_digit: int) -> GuardedBorderPath:
    return GuardedBorderPath(
        BoundaryPathKind.THREE_BORDER_RETURN,
        entry_digit,
        exit_digit,
    )


__all__ = [
    "CYCLE_0563",
    "CYCLE_89",
    "CYCLE_421",
    "CYCLE_4721",
    "CYCLE_26847",
    "ENTRY_0563",
    "ENTRY_89_AT_NINE",
    "ENTRY_421",
    "ENTRY_4721",
    "ENTRY_26847_PHASES",
    "PATH_305",
    "PATH_630",
    "BorderEntryPort",
    "BorderExitPort",
    "BoundaryActionIdentity",
    "BoundaryOccurrence",
    "BoundaryPathKind",
    "ClosedBorderCycle",
    "CollatzSegmentIdentity",
    "CycleEntryPhase",
    "GuardedBorderPath",
    "NonBorderSegment",
    "border_return_path",
    "cycle_phase",
    "is_boundary_occurrence",
]
