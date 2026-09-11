"""Fresh-runtime factory sharing only the immutable C4 upstream summary DAG."""

from dataclasses import dataclass

from devtools.proofs.c4_summary_artifact import c4_fourth_right_summary
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from tests.support.diamond_query import build


@dataclass(frozen=True, slots=True)
class C4FourthSummary:
    runtime: DiamondRuntime
    pair: ActionProgramID
    fourth: ActionProgramID
    closure: ClosureProgramID


@dataclass(frozen=True, slots=True)
class C4FourthInput:
    runtime: DiamondRuntime
    pair: ActionProgramID
    fourth: ActionProgramID
    cell: CellID


def fresh_c4_fourth_input() -> C4FourthInput:
    application = build(PhysicalCollatzFourBlockEffect(), (0, 1) * 8, 16, 1)
    runtime, primitive = application.runtime, application.root
    runtime.kernel(primitive)
    pair = runtime.actions.compose(primitive, primitive)
    fourth = runtime.actions.compose(pair, pair)
    return C4FourthInput(runtime, pair, fourth, runtime.cells.source(0, 4))


def fresh_c4_fourth_right_summary() -> C4FourthSummary:
    value = fresh_c4_fourth_input()
    closure = c4_fourth_right_summary(value.runtime, value.fourth, value.cell)
    return C4FourthSummary(value.runtime, value.pair, value.fourth, closure)


__all__ = [
    "C4FourthInput",
    "C4FourthSummary",
    "fresh_c4_fourth_input",
    "fresh_c4_fourth_right_summary",
]
