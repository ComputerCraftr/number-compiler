"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ExactSource,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID


def machine(
    effect: BlockEffect | None = None,
) -> tuple[DiamondRuntime, ActionProgramID]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(CollatzPhysicalBlockEffect() if effect is None else effect)
    geometry = SourceGeometry(ledger, ExactSource((1, 1), 2, "collatz", 2, 8))
    geometry.span((1, 1), 2, 8)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(atom)
    runtime.kernel(action)
    return runtime, action


def normalize(runtime: DiamondRuntime, function: ExprID) -> ExprID:
    result = runtime.execute(NormalizePrimitiveLambda(function))
    assert type(result) is ExprID
    return result


def literal(
    runtime: DiamondRuntime, action: ActionProgramID, side: int, value: int
) -> ExprID:
    return runtime.higher.expressions.literal(
        runtime.boundaries.literal(action, side, value)
    )


def advance_after_emit(
    arena: BoundaryExpressionArena, action: ActionProgramID, left: ExprID, right: ExprID
) -> tuple[ExprID, ExprID, ExprID]:
    """Build the same dependent primitive recipe for finite/compiler boundary tests."""
    symbol = arena.primitive_emit(action, left, arena.symbol(action, 1), right)
    body = arena.primitive_advance(action, 0, left, symbol)
    return symbol, body, arena.lambda_(right, body)


def incoming_advance_task(
    runtime: DiamondRuntime,
    action: ActionProgramID,
) -> tuple[BoundaryExpressionArena, CompilePrimitiveFunction]:
    arena = runtime.higher.expressions
    variable = arena.variable(arena.state_sort(action, 0), "incoming")
    body = arena.primitive_advance(action, 0, variable, arena.symbol(action, 1))
    task = CompilePrimitiveFunction(variable, body)
    return arena, task
