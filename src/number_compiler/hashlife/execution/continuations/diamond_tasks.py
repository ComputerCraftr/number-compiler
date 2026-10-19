"""Typed dependencies for the iterative output-complete diamond evaluator."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
    ResolveExpr,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherTask,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    ContinuationTask,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionID,
    BoundaryStateID,
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.interfaces.semantic_expression_tasks import StructuredTask
from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
    PrimitiveMacroTask,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    DiamondQuotientID,
    StructureID,
)


@dataclass(frozen=True, slots=True)
class Initial:
    action: ActionProgramID
    side: int


@dataclass(frozen=True, slots=True)
class Transfer:
    """Observe a parametric diamond at a finite structured boundary value."""

    provider: ImageBinding
    action: ActionProgramID
    state: BoundaryStateID
    side: int


@dataclass(frozen=True, slots=True)
class ResetTransfer:
    """A complete synchronizing transfer, independent of its incoming state."""

    provider: ImageBinding
    action: ActionProgramID
    side: int


@dataclass(frozen=True, slots=True)
class Substitute:
    step: ContinuationStep
    argument: BoundaryStateID


@dataclass(frozen=True, slots=True)
class Evaluate:
    function: BoundaryActionID
    argument: BoundaryStateID


@dataclass(frozen=True, slots=True)
class Output:
    """One transient output observation; this task is never memoized."""

    provider: ImageBinding
    action: ActionProgramID
    left: BoundaryStateID
    right: BoundaryStateID


@dataclass(frozen=True, slots=True)
class OutputFunction:
    """Complete function of the free original symbol, without a cell binding."""

    provider: ActionProgramID
    provider_left: BoundaryStateID
    provider_right: BoundaryStateID
    action: ActionProgramID
    left: BoundaryStateID
    right: BoundaryStateID


@dataclass(frozen=True, slots=True)
class MacroTransferKey:
    before: ActionProgramID
    after: ActionProgramID
    cell: CellID
    side: int


@dataclass(frozen=True, slots=True)
class PairSummary:
    action: ActionProgramID
    cell: CellID


@dataclass(frozen=True, slots=True)
class SpatialSummary:
    """A complete primitive transfer on one original-source parent."""

    action: ActionProgramID
    cell: CellID
    side: int


Task: TypeAlias = (
    Initial
    | Transfer
    | ResetTransfer
    | Substitute
    | Evaluate
    | Output
    | OutputFunction
    | PairSummary
    | SpatialSummary
    | ContextObservation
    | HigherTask
    | LowerFinite
    | ResolveExpr
    | ContinuationTask
    | StructuredTask
    | PrimitiveMacroTask
)
Result: TypeAlias = (
    BoundaryStateID | TransferSummaryID | ExprID | StructureID | DiamondQuotientID | int
)
