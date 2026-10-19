"""Exact finite F5 actions driven by source-authenticated carry words."""

from __future__ import annotations

from dataclasses import dataclass

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


__all__ = ["DigitCarryAffine"]
