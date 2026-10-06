"""Exact active-width walk summaries for admitted spatial and temporal actions."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety


@dataclass(frozen=True, slots=True)
class BlankLedger:
    """Width displacement and extrema, including the initial and final widths.

    This is an output summary. Repeating it does not authenticate repetition
    of the source action that produced it.
    """

    delta: int = 0
    minimum: int = 0
    maximum: int = 0

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in self.as_tuple()):
            raise TypeError("blank ledger requires exact integers")
        PrefixSafety(self.delta, self.minimum)
        PrefixSafety(-self.delta, -self.maximum)

    def as_tuple(self) -> tuple[int, int, int]:
        return self.delta, self.minimum, self.maximum

    @classmethod
    def _from_bounds(cls, lower: PrefixSafety, upper: PrefixSafety) -> BlankLedger:
        return cls(lower.delta, lower.minimum, -upper.minimum)

    def then(self, after: BlankLedger) -> BlankLedger:
        """Compose chronological walks without visiting their intermediate widths."""
        if type(after) is not BlankLedger:
            raise TypeError("blank ledger composition requires another blank ledger")
        lower = PrefixSafety(self.delta, self.minimum).then(
            PrefixSafety(after.delta, after.minimum)
        )
        upper = PrefixSafety(-self.delta, -self.maximum).then(
            PrefixSafety(-after.delta, -after.maximum)
        )
        return self._from_bounds(lower, upper)

    def repeat(self, copies: int) -> BlankLedger:
        """Repeat the summary by closed prefix formulas, not a loop over copies."""
        return self._from_bounds(
            PrefixSafety(self.delta, self.minimum).repeat(copies),
            PrefixSafety(-self.delta, -self.maximum).repeat(copies),
        )
