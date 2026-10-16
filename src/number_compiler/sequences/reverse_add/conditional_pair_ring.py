"""Input-driven Moore and temporal matrix actions for reverse/add Q19 cells.

The ring's input alphabet is source-certified growth, previous pair, and
forward/reflected carry ingresses.  These are *not* the 2rev10 threshold/digit
ports.  The time operator is a partial function on 19 pair coefficients.

Action composition and formal binary powers do not certify repetition of an
input program on future physical sources. Only the actual finite inlet word
from an issued reverse/add ring has physical source authority.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_observer import (
    partition_by_signature,
    refine_observer_partition,
)
from number_compiler.arithmetic.functions.partial_count_action import (
    ActionUniverse,
    PartialCountAction,
)

from .inward_bank_harmonics import BANDS, pair_band, pair_carry


@dataclass(frozen=True, slots=True)
class RingPairLetter:
    """One physical conditional input to one inward Q19 coefficient."""

    position: int
    growth: int
    previous_pair: int | None
    low_carry: int
    reflected_carry: int

    def __post_init__(self) -> None:
        if (
            type(self.position) is not int
            or self.position < 0
            or type(self.growth) is not int
            or self.growth not in (0, 1)
            or type(self.low_carry) is not int
            or self.low_carry not in (0, 1)
            or type(self.reflected_carry) is not int
            or self.reflected_carry not in (0, 1)
        ):
            raise ValueError("bad conditional pair input")
        if self.growth and self.position > 0:
            if type(self.previous_pair) is not int or not 0 <= self.previous_pair <= 18:
                raise ValueError("growth interior needs a source adjacent pair")
        elif self.previous_pair is not None:
            raise ValueError("unused previous pair must be punctured")

    def successor(self, pair: int) -> int | None:
        """Actual growth/quiet polynomial under these *supplied* Q19 ports."""
        if type(pair) is not int or not 0 <= pair <= 18:
            raise ValueError("Q19 state outside 0..18")
        a, b = self.low_carry, self.reflected_carry
        if self.growth and self.position == 0:
            out = pair + 1 - 10 * pair_carry(pair, 0)
        elif self.growth:
            assert self.previous_pair is not None
            high_out = pair_carry(pair, b)
            out = (
                self.previous_pair
                + pair
                + a
                + high_out
                - 10 * (pair_carry(pair, a) + pair_carry(self.previous_pair, high_out))
            )
        else:
            out = 2 * pair + a + b - 10 * (pair_carry(pair, a) + pair_carry(pair, b))
        return out if 0 <= out <= 18 else None


@dataclass(frozen=True, slots=True)
class ConditionalRingPairAction:
    """Partial 19-state action, five-band output counts, and growth writer."""

    _action: PartialCountAction

    def __post_init__(self) -> None:
        if (
            type(self._action) is not PartialCountAction
            or self._action.owner.states != 19
            or self._action.owner.channels != len(BANDS) + 1
        ):
            raise ValueError("bad conditional ring action")

    @property
    def duration(self) -> int:
        return self._action.steps

    @property
    def targets(self) -> tuple[int | None, ...]:
        return self._action.targets

    @property
    def band_counts(self) -> tuple[tuple[int, ...] | None, ...]:
        return tuple(
            None if row is None else row[: len(BANDS)] for row in self._action.counts
        )

    @property
    def growth_count(self) -> int:
        rows = tuple(row for row in self._action.counts if row is not None)
        if not rows:
            raise ValueError("conditional action has no admitted source state")
        counts = {row[-1] for row in rows}
        if len(counts) != 1:
            raise AssertionError("growth output changed across admitted pair states")
        return counts.pop()

    @property
    def physical_input_repeat_certified(self) -> bool:
        return False

    @classmethod
    def identity(cls, owner: ActionUniverse | None = None) -> ConditionalRingPairAction:
        universe = ActionUniverse(19, len(BANDS) + 1) if owner is None else owner
        if universe.states != 19 or universe.channels != len(BANDS) + 1:
            raise ValueError("wrong Q19 action universe")
        return cls(PartialCountAction.identity(universe))

    @classmethod
    def letter(
        cls, port: RingPairLetter, owner: ActionUniverse | None = None
    ) -> ConditionalRingPairAction:
        universe = ActionUniverse(19, len(BANDS) + 1) if owner is None else owner
        if universe.states != 19 or universe.channels != len(BANDS) + 1:
            raise ValueError("wrong Q19 action universe")
        targets = tuple(port.successor(q) for q in range(19))
        counts: list[tuple[int, ...] | None] = []
        for target in targets:
            if target is None:
                counts.append(None)
            else:
                values = [0] * len(BANDS)
                values[BANDS.index(pair_band(target))] = 1
                counts.append((*values, port.growth))
        return cls(PartialCountAction(1, targets, tuple(counts), universe))

    def then(self, later: ConditionalRingPairAction) -> ConditionalRingPairAction:
        """Compose a source-specific FIRST action then a LATER port action."""
        if type(later) is not ConditionalRingPairAction:
            raise TypeError(
                "Q19 action composition requires another conditional action"
            )
        return ConditionalRingPairAction(self._action.then(later._action))

    def formal_power(self, repetitions: int) -> ConditionalRingPairAction:
        """O(log k) algebraic repeat of *hypothetical* identical inlet word.

        The returned action cannot authenticate a physical future by itself.
        """
        return ConditionalRingPairAction(self._action.power(repetitions))


def input_driven_moore_classes(
    letters: tuple[RingPairLetter, ...],
    *,
    observation: str = "five_band",
) -> tuple[int, ...]:
    """Complete future Moore refinement over ALL declared input letters.

    This minimizes the 19 local coefficient states for an *input alphabet*;
    it does not claim that a physical source emits this inlet language forever.
    """
    if type(letters) is not tuple or not letters:
        raise ValueError("Moore refinement requires an input alphabet")
    if observation not in ("five_band", "gt_high", "eq", "f5", "coefficient"):
        raise ValueError("unknown Q19 observation contract")
    labels = tuple(
        pair_band(q)
        if observation == "five_band"
        else int(pair_band(q) == observation)
        if observation in ("gt_high", "eq")
        else q % 5
        if observation == "f5"
        else q
        for q in range(19)
    )
    alphabet = tuple(dict.fromkeys(letters))
    rows = tuple(tuple(letter.successor(q) for letter in alphabet) for q in range(19))
    classes = partition_by_signature(labels)
    for _ in range(19):
        next_classes = refine_observer_partition(rows, labels, classes)
        if next_classes == classes:
            return classes
        classes = next_classes
    raise AssertionError("19-state Moore partition failed to stabilize")


__all__ = ["ConditionalRingPairAction", "RingPairLetter", "input_driven_moore_classes"]
