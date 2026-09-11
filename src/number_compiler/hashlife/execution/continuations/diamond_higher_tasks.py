"""Typed dependencies for source-parametric higher bimachine expressions."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID


@dataclass(frozen=True, slots=True)
class HigherInitial:
    action: ActionProgramID
    side: int


@dataclass(frozen=True, slots=True)
class HigherStep:
    action: ActionProgramID
    side: int
    state: ExprID
    symbol: ExprID


@dataclass(frozen=True, slots=True)
class HigherEmit:
    """An output expression request; bound observations are never memoized."""

    action: ActionProgramID
    left: ExprID
    symbol: ExprID
    right: ExprID


@dataclass(frozen=True, slots=True)
class HigherSummary:
    provider: ActionProgramID
    consumer: ActionProgramID
    cell: CellID


@dataclass(frozen=True, slots=True)
class HigherUnarySummary:
    action: ActionProgramID
    cell: CellID
    side: int


@dataclass(frozen=True, slots=True)
class HigherObserve:
    summary: TransferSummaryID
    left: ExprID
    right: ExprID
    incoming: ExprID
    side: int


@dataclass(frozen=True, slots=True)
class HigherUnaryObserve:
    summary: TransferSummaryID
    state: ExprID


HigherTask: TypeAlias = (
    HigherInitial
    | HigherStep
    | HigherEmit
    | HigherSummary
    | HigherUnarySummary
    | HigherObserve
    | HigherUnaryObserve
)
HigherResult: TypeAlias = ExprID | TransferSummaryID

HIGHER_TASK_TYPES = (
    HigherInitial,
    HigherStep,
    HigherEmit,
    HigherSummary,
    HigherUnarySummary,
    HigherObserve,
    HigherUnaryObserve,
)
