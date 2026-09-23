"""Immutable records for dyadic source-image execution."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer


@dataclass(frozen=True, slots=True)
class DyadicReturnLaw:
    """Pinned two-branch law with denominator two."""

    family: str
    semantic_version: str
    gains: tuple[int, int]
    offsets: tuple[int, int]
    weights: tuple[int, int]
    cycle: DyadicReturnCycle | None = None

    def __post_init__(self) -> None:
        if type(self.family) is not str or not self.family:
            raise ValueError("dyadic return family must be nonempty")
        if type(self.semantic_version) is not str or not self.semantic_version:
            raise ValueError("dyadic return version must be nonempty")
        for label, values in (
            ("gains", self.gains),
            ("offsets", self.offsets),
            ("weights", self.weights),
        ):
            if (
                type(values) is not tuple
                or len(values) != 2
                or any(type(v) is not int for v in values)
            ):
                raise TypeError(f"dyadic return {label} must be a pair of integers")
        if any(value <= 0 for value in self.gains):
            raise ValueError("dyadic return gains must be positive")
        even_value = self.offsets[0]
        odd_value = self.gains[1] + self.offsets[1]
        if even_value < 0 or even_value % 2:
            raise ValueError("even dyadic branch is not a nonnegative integer map")
        if odd_value < 0 or odd_value % 2:
            raise ValueError("odd dyadic branch is not a nonnegative integer map")
        if self.cycle is not None:
            if type(self.cycle) is not DyadicReturnCycle:
                raise TypeError("dyadic return cycle has an invalid descriptor")
            self.cycle.validate(self)

    @property
    def descriptor(
        self,
    ) -> tuple[
        str,
        str,
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, ...] | None,
    ]:
        return (
            self.family,
            self.semantic_version,
            self.gains,
            self.offsets,
            self.weights,
            None if self.cycle is None else self.cycle.descriptor,
        )


@dataclass(frozen=True, slots=True)
class DyadicReturnCycle:
    """A finite cycle of exact states for one pinned dyadic law."""

    states: tuple[int, ...]

    @property
    def descriptor(self) -> tuple[int, ...]:
        return self.states

    def validate(self, law: DyadicReturnLaw) -> None:
        if type(self.states) is not tuple or not self.states:
            raise ValueError("dyadic return cycle requires nonempty states")
        if len(self.states) > 64:
            raise ValueError("dyadic return cycle is too large to validate")
        if any(type(state) is not int or state < 0 for state in self.states):
            raise ValueError("dyadic return cycle states must be nonnegative integers")
        if len(set(self.states)) != len(self.states):
            raise ValueError("dyadic return cycle states must be distinct")
        for index, state in enumerate(self.states):
            bit = state & 1
            numerator = law.gains[bit] * state + law.offsets[bit]
            if (
                numerator % 2
                or numerator // 2 != self.states[(index + 1) % len(self.states)]
            ):
                raise ValueError("dyadic return cycle does not satisfy its law")


@dataclass(frozen=True, slots=True)
class DyadicReturnActionID(ArenaHandle):
    """Authenticated action for an exact number of physical steps."""


@dataclass(frozen=True, slots=True)
class DyadicReturnSourceID(ArenaHandle):
    """Authenticated local source residue and its discarded high lift."""


@dataclass(frozen=True, slots=True)
class DyadicReturnSupportID(ArenaHandle):
    """Chronological branch support for a physical image."""


@dataclass(frozen=True, slots=True)
class DyadicReturnImageID(ArenaHandle):
    """Authenticated exact image payload."""


@dataclass(frozen=True, slots=True)
class _ActionNode:
    width: int
    children: tuple[DyadicReturnActionID, DyadicReturnActionID] | None


@dataclass(frozen=True, slots=True)
class _SourceNode:
    residue: int
    precision: int
    lift: int
    parent: DyadicReturnSourceID | None
    parent_action: DyadicReturnActionID | None
    before_image: DyadicReturnImageID | None
    side: int
    exact: bool = False


@dataclass(frozen=True, slots=True)
class _SupportNode:
    width: int
    residue: int
    transfer: SkewTransfer[int]
    odd_steps: int
    delta: int
    minimum: int
    branch_word: int | None
    children: tuple[DyadicReturnSupportID, DyadicReturnSupportID] | None
    cycle: DyadicCycleSummary | None = None


@dataclass(frozen=True, slots=True)
class DyadicCycleSummary:
    """Compressed exact singleton tail metadata."""

    entry_steps: int
    cycle_phase: int
    cycles: int
    remainder: int
    terminal_phase: int
    odd_steps: int
    delta: int
    minimum: int


@dataclass(frozen=True, slots=True)
class DyadicAggregateSummary:
    """Demanded arithmetic/clock projection, without chronological support.

    This is not successor authority. The authenticated image remains owned by
    the scheduler, including support needed for first-failure descent.
    """

    width: int
    residue: int
    transfer: SkewTransfer[int]
    delta: int
    minimum: int
    odd_steps: int
    cycle: DyadicCycleSummary | None


@dataclass(frozen=True, slots=True)
class DyadicImageSummary:
    """Exact affine result and retained chronological support."""

    width: int
    residue: int
    transfer: SkewTransfer[int]
    delta: int
    minimum: int
    odd_steps: int
    support: DyadicReturnSupportID | None
    cycle: DyadicCycleSummary | None = None


@dataclass(frozen=True, slots=True)
class _ImageNode:
    source: DyadicReturnSourceID
    action: DyadicReturnActionID
    summary: DyadicImageSummary
