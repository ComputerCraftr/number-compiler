"""Exact finite F5 actions driven by source-authenticated carry words."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from number_compiler.arithmetic.fields.morphism_core import binary_power


@dataclass(frozen=True, slots=True)
class DigitCarryAffine:
    """Carry action ``r -> multiplier*r + offset`` over F5.

    Phase counts use action-relative physical tick modulo four, starting at
    phase zero for this action. A source-border phase is separate metadata;
    these counts describe only the supplied finite word and assert no future
    word.
    """

    physical_ticks: int
    multiplier: int
    offset: int
    phase_counts: tuple[int, int, int, int]

    def __post_init__(self) -> None:
        if (
            type(self.physical_ticks) is not int
            or self.physical_ticks < 0
            or type(self.multiplier) is not int
            or self.multiplier != pow(2, self.physical_ticks, 5)
            or type(self.offset) is not int
            or not 0 <= self.offset < 5
            or type(self.phase_counts) is not tuple
            or len(self.phase_counts) != 4
            or any(type(count) is not int or count < 0 for count in self.phase_counts)
            or sum(self.phase_counts) > self.physical_ticks
        ):
            raise ValueError("invalid exact F5 carry action")

    @classmethod
    def identity(cls) -> DigitCarryAffine:
        return cls(0, 1, 0, (0, 0, 0, 0))

    @classmethod
    def two_step(cls, first: int, second: int) -> DigitCarryAffine:
        if (
            type(first) is not int
            or type(second) is not int
            or first not in (0, 1)
            or second not in (0, 1)
        ):
            raise ValueError("two-step carries must be Boolean")
        return cls(2, 4, (2 * first + second) % 5, (first, second, 0, 0))

    def then(self, later: DigitCarryAffine) -> DigitCarryAffine:
        if type(later) is not DigitCarryAffine:
            raise TypeError("expected an exact digit carry action")
        counts = list(self.phase_counts)
        shift = self.physical_ticks % 4
        for phase, count in enumerate(later.phase_counts):
            counts[(phase + shift) % 4] += count
        return DigitCarryAffine(
            self.physical_ticks + later.physical_ticks,
            self.multiplier * later.multiplier % 5,
            (later.multiplier * self.offset + later.offset) % 5,
            (counts[0], counts[1], counts[2], counts[3]),
        )

    def power(self, copies: int) -> DigitCarryAffine:
        """Compose a repeated word after its repetition has been certified."""
        if type(copies) is not int or copies < 0:
            raise ValueError("carry-action power needs a nonnegative count")
        return binary_power(
            self,
            copies,
            identity=self.identity(),
            compose=lambda first, later: first.then(later),
        ).value

    def apply(self, residue: int) -> int:
        if type(residue) is not int or not 0 <= residue < 5:
            raise ValueError("digit residue must belong to F5")
        return (self.multiplier * residue + self.offset) % 5


class Seed196BandPhase(Enum):
    """Source-closed low-band transformations for the seed-196 orbit."""

    ENTRY = "entry"
    FIRST = "first"
    SECOND = "second"
    THIRD = "third"


class Seed196BandSheet(Enum):
    """The two consecutive T-squared actions in each four-tick block."""

    PHASE_ZERO = "phase_zero"
    AFTER_FIRST_PAIR = "after_first_pair"


_SEED196_NEXT = {
    Seed196BandPhase.ENTRY: Seed196BandPhase.FIRST,
    Seed196BandPhase.FIRST: Seed196BandPhase.SECOND,
    Seed196BandPhase.SECOND: Seed196BandPhase.THIRD,
    Seed196BandPhase.THIRD: Seed196BandPhase.FIRST,
}
_SEED196_THRESHOLD_WRITERS = {
    Seed196BandPhase.ENTRY: 0b10011,
    Seed196BandPhase.FIRST: 0b00111,
    Seed196BandPhase.SECOND: 0b10111,
    Seed196BandPhase.THIRD: 0b01011,
}
_SEED196_X4 = {
    Seed196BandPhase.ENTRY: 3488,
    Seed196BandPhase.FIRST: 1568,
    Seed196BandPhase.SECOND: 988,
    Seed196BandPhase.THIRD: 8388,
}


@dataclass(frozen=True, slots=True)
class Seed196TwoBaseBand:
    """Seed-196 low-four-digit action at even physical generations >= 16.

    The finite source quotient certifies four low decimal digits and its
    intermediate paired sheet. It does not represent a full numeral or
    license higher-annulus queries.
    """

    phase: Seed196BandPhase
    sheet: Seed196BandSheet = Seed196BandSheet.PHASE_ZERO

    def __post_init__(self) -> None:
        if (
            type(self.phase) is not Seed196BandPhase
            or type(self.sheet) is not Seed196BandSheet
        ):
            raise ValueError("outside the source-certified seed-196 low-band action")

    @classmethod
    def entry(cls) -> Seed196TwoBaseBand:
        """The actual generation-16 source is admitted as the entry class."""
        return cls(Seed196BandPhase.ENTRY)

    @property
    def low_four(self) -> int:
        """Return the exact issued low-four decimal digits as an integer."""
        low = _SEED196_X4[self.phase]
        if self.sheet is Seed196BandSheet.PHASE_ZERO:
            return low
        mask = _SEED196_THRESHOLD_WRITERS[self.phase]
        threshold_low = 0
        for index in reversed(range(4)):
            threshold_low = 10 * threshold_low + ((mask >> index) & 1)
        return (40 * low - 198 * threshold_low) % 10_000

    def next_pair(self) -> Seed196TwoBaseBand:
        if self.sheet is Seed196BandSheet.PHASE_ZERO:
            return type(self)(self.phase, Seed196BandSheet.AFTER_FIRST_PAIR)
        return type(self)(_SEED196_NEXT[self.phase], Seed196BandSheet.PHASE_ZERO)

    def next_four(self) -> Seed196TwoBaseBand:
        if self.sheet is not Seed196BandSheet.PHASE_ZERO:
            raise ValueError("four-generation macro needs the phase-zero sheet")
        return type(self)(_SEED196_NEXT[self.phase], Seed196BandSheet.PHASE_ZERO)

    @classmethod
    def at_even_generation(
        cls,
        physical_generation: int,
    ) -> Seed196TwoBaseBand:
        """Index the admitted quotient without replaying source generations."""
        if (
            type(physical_generation) is not int
            or physical_generation < 16
            or physical_generation % 2
        ):
            raise ValueError("low-band action needs an even generation >= 16")
        half_returns, after_first_pair = divmod((physical_generation - 16) // 2, 2)
        if half_returns == 0:
            phase = Seed196BandPhase.ENTRY
        else:
            recurrent = (
                Seed196BandPhase.FIRST,
                Seed196BandPhase.SECOND,
                Seed196BandPhase.THIRD,
            )
            phase = recurrent[(half_returns - 1) % len(recurrent)]
        sheet = (
            Seed196BandSheet.AFTER_FIRST_PAIR
            if after_first_pair
            else Seed196BandSheet.PHASE_ZERO
        )
        return cls(phase, sheet)


def seed196_low_four_digits_at_even_generation(
    physical_generation: int,
) -> int:
    """Return the seed-196 lower four digits at an admitted even generation."""
    state = Seed196TwoBaseBand.at_even_generation(physical_generation)
    return state.low_four


__all__ = [
    "DigitCarryAffine",
    "Seed196BandPhase",
    "Seed196BandSheet",
    "Seed196TwoBaseBand",
    "seed196_low_four_digits_at_even_generation",
]
