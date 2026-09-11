"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ExactSource,
    TransferSummaryID,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherEmit,
    HigherInitial,
    HigherUnaryObserve,
    HigherUnarySummary,
)
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import Task
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
        TransferSummaryID,
    )
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID


def machine(
    bits: tuple[int, ...] = (1, 1, 0, 1, 1), extent: int = 8
) -> tuple[DiamondRuntime, ActionProgramID]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    primitive = compiler.atom(CollatzPhysicalBlockEffect())
    geometry = SourceGeometry(ledger, ExactSource(bits, 2, "collatz", 2, extent))
    geometry.span(bits, 2, extent)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(primitive)
    return runtime, action


def expr(runtime: DiamondRuntime, task: Task) -> ExprID:
    result = runtime.execute(task)
    assert type(result) is ExprID
    return result


def scalar(runtime: DiamondRuntime, expression: ExprID) -> int:
    result = runtime.execute(LowerFinite(expression))
    assert type(result) is int
    return result


def summary(runtime: DiamondRuntime, task: Task) -> TransferSummaryID:
    result = runtime.execute(task)
    assert type(result) is TransferSummaryID
    return result


def point(runtime: DiamondRuntime, action: ActionProgramID, position: int) -> int:
    left = expr(runtime, HigherInitial(action, 0))
    right = expr(runtime, HigherInitial(action, 1))
    extent = runtime.cells.source_geometry._construction.source.extent
    assert extent is not None
    for _, cell in runtime.cells.source_span(0, position):
        transfer = summary(runtime, HigherUnarySummary(action, cell, 0))
        left = expr(runtime, HigherUnaryObserve(transfer, left))
    for _, cell in reversed(
        runtime.cells.source_span(position + 1, extent - position - 1)
    ):
        transfer = summary(runtime, HigherUnarySummary(action, cell, 1))
        right = expr(runtime, HigherUnaryObserve(transfer, right))
    original = runtime.cells.source_geometry.read(position)
    symbol = runtime.higher.expressions.symbol(action, original)
    return scalar(runtime, expr(runtime, HigherEmit(action, left, symbol, right)))
