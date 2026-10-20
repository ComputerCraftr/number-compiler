"""Immutable records and scoped handles for higher K/U summaries."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
    HigherFunctionID,
)
from number_compiler.hashlife.execution.field_images import SourceCellID


@dataclass(frozen=True, slots=True)
class HigherSummaryID(ArenaHandle):
    """Scoped canonical K/U semantic summary."""


@dataclass(frozen=True, slots=True)
class UnarySummary:
    action: FieldCellActionID
    side: int
    function: HigherFunctionID
    recipe: UnaryRecipe = field(compare=False, hash=False)


@dataclass(frozen=True, slots=True)
class ContextSummary:
    provider: FieldCellActionID
    consumer: FieldCellActionID
    left: HigherExpressionID
    right: HigherExpressionID
    incoming_left: HigherExpressionID
    incoming_right: HigherExpressionID
    left_body: HigherExpressionID
    right_body: HigherExpressionID
    recipe: ContextRecipe = field(compare=False, hash=False)


@dataclass(frozen=True, slots=True)
class UnaryLeaf:
    symbol: int


@dataclass(frozen=True, slots=True)
class UnaryIdentity:
    pass


@dataclass(frozen=True, slots=True)
class UnaryFinite:
    """Complete bounded primitive port function, never an emitted tape."""

    outputs: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.outputs) is not tuple
            or not 1 <= len(self.outputs) <= 64
            or any(
                type(value) is not int or not 0 <= value < len(self.outputs)
                for value in self.outputs
            )
        ):
            raise ValueError("finite unary transfer has an invalid bounded port")


@dataclass(frozen=True, slots=True)
class UnaryAffine:
    """A bounded modular port action; its payload never grows with cell width."""

    transfer: RadixRemainderTransfer


@dataclass(frozen=True, slots=True)
class UnarySpatial:
    first: HigherSummaryID
    second: HigherSummaryID


@dataclass(frozen=True, slots=True)
class UnaryTemporal:
    forward: HigherSummaryID
    opposite: HigherSummaryID
    context: HigherSummaryID


UnaryRecipe = (
    UnaryIdentity | UnaryFinite | UnaryAffine | UnaryLeaf | UnarySpatial | UnaryTemporal
)


@dataclass(frozen=True, slots=True)
class ContextLeaf:
    symbol: int


@dataclass(frozen=True, slots=True)
class ContextSpatial:
    low: HigherSummaryID
    high: HigherSummaryID
    low_forward: HigherSummaryID
    high_backward: HigherSummaryID


ContextRecipe = ContextLeaf | ContextSpatial


@dataclass(frozen=True, slots=True)
class RuntimeUnarySummary:
    action: FieldCellActionID
    side: int
    recipe: UnaryRecipe


@dataclass(frozen=True, slots=True)
class RuntimeContextSummary:
    provider: FieldCellActionID
    consumer: FieldCellActionID
    recipe: ContextRecipe


SummaryRecord = (
    UnarySummary | ContextSummary | RuntimeUnarySummary | RuntimeContextSummary
)


@dataclass(frozen=True, slots=True)
class UnaryBinding:
    action: FieldCellActionID
    source: SourceCellID
    side: int


@dataclass(frozen=True, slots=True)
class ContextBinding:
    provider: FieldCellActionID
    consumer: FieldCellActionID
    source: SourceCellID


__all__ = [
    "ContextBinding",
    "ContextLeaf",
    "ContextSpatial",
    "ContextSummary",
    "HigherSummaryID",
    "RuntimeContextSummary",
    "RuntimeUnarySummary",
    "SummaryRecord",
    "UnaryAffine",
    "UnaryBinding",
    "UnaryFinite",
    "UnaryIdentity",
    "UnaryLeaf",
    "UnaryRecipe",
    "UnarySpatial",
    "UnarySummary",
    "UnaryTemporal",
]
