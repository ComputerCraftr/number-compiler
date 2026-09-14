"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import StateSort
from tests.support.diamond_higher_context import machine

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
        TransferSummaryID,
    )
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID


def populated() -> tuple[
    DiamondRuntime,
    ActionProgramID,
    ExprID,
    ExprID,
    CompilePrimitiveFunction,
    TransferSummaryID,
]:
    runtime, action = machine()
    runtime.kernel(action)
    arena = runtime.higher.expressions
    variable = arena.variable(StateSort(action, 0), "primitive-input")
    expression = arena.primitive_advance(action, 0, variable, arena.symbol(action, 1))
    request = CompilePrimitiveFunction(variable, expression)
    function = runtime.execute(request)
    assert runtime.primitive_continuations.maps[request] == function
    return runtime, action, variable, expression, request, function
