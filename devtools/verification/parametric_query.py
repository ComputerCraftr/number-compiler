"""Exact closure-carrier observation oracle for adversarial proof tests."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherEmit,
    HigherInitial,
    HigherObserve,
    HigherSummary,
    HigherUnaryObserve,
    HigherUnarySummary,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.observation.diamond_parametric_query import (
    admit_point,
    admit_width,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import Result


def _expr(result: Result) -> ExprID:
    if type(result) is not ExprID:
        raise AssertionError("parametric boundary query returned the wrong result kind")
    return result


def _summary(result: Result) -> TransferSummaryID:
    if type(result) is not TransferSummaryID:
        raise AssertionError("parent compilation returned the wrong result kind")
    return result


def _scalar(result: Result) -> int:
    if type(result) is not int:
        raise AssertionError("finite observation returned a structured value")
    return result


def _transfer(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    cell: CellID,
    state: ExprID,
    side: int,
) -> ExprID:
    parent = _summary(runtime.execute(HigherUnarySummary(action, cell, side)))
    return _expr(runtime.execute(HigherUnaryObserve(parent, state)))


@source_reads_only
def parametric_point(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    position: int,
) -> int:
    source = admit_point(runtime, action, position)
    left = _expr(runtime.execute(HigherInitial(action, 0)))
    right = _expr(runtime.execute(HigherInitial(action, 1)))
    forest = runtime.point_span(action, position, source.length)
    selected: CellID | None = None
    origin = 0
    for start, cell in forest:
        end = start + runtime.cells.node(cell).width
        if end <= position:
            left = _transfer(runtime, action, cell, left, 0)
        elif start <= position:
            selected, origin = cell, start
    for start, cell in reversed(forest):
        if start > position:
            right = _transfer(runtime, action, cell, right, 1)
    assert selected is not None
    # Probe each required direction on the selected parent before child
    # descent. An extreme coordinate needs only one direction; compiling its
    # unused opposite continuation would force work outside this observation.
    local = position - origin
    if local:
        runtime.execute(HigherUnarySummary(action, selected, 0))
    if local + 1 < runtime.cells.node(selected).width:
        runtime.execute(HigherUnarySummary(action, selected, 1))
    while runtime.cells.node(selected).level:
        low, high = runtime.cells.split(selected)
        middle = origin + runtime.cells.node(low).width
        runtime.ledger.bump("parametric_point_descent_steps")
        if position < middle:
            right = _transfer(runtime, action, high, right, 1)
            selected = low
        else:
            left = _transfer(runtime, action, low, left, 0)
            selected, origin = high, middle
    symbol = runtime.higher.expressions.symbol(
        action, runtime.cells.source_symbol(selected)
    )
    output = _expr(runtime.execute(HigherEmit(action, left, symbol, right)))
    return _scalar(runtime.execute(LowerFinite(output)))


@dataclass(frozen=True, slots=True)
class _SourceContext:
    start: int
    cell: CellID
    left: ExprID


def _active(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    observer: ActionProgramID,
    cell: CellID,
    left: ExprID,
    right: ExprID,
    incoming: ExprID,
) -> bool:
    parent = _summary(runtime.execute(HigherSummary(action, observer, cell)))
    expression = _expr(runtime.execute(HigherObserve(parent, left, right, incoming, 1)))
    value = _scalar(runtime.execute(LowerFinite(expression)))
    if value not in (0, 1):
        raise AssertionError("activity observer left its finite Boolean domain")
    return value == 1


@source_reads_only
def parametric_width(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    observer: ActionProgramID,
    maxwidth: int,
) -> int:
    source = admit_width(runtime, action, observer, maxwidth)
    if not maxwidth:
        return 0
    left = _expr(runtime.execute(HigherInitial(action, 0)))
    right = _expr(runtime.execute(HigherInitial(action, 1)))
    incoming = _expr(runtime.execute(HigherInitial(observer, 1)))
    forest = runtime.cells.source_span(0, maxwidth)
    contexts: list[_SourceContext] = []
    for index, (start, cell) in enumerate(forest):
        contexts.append(_SourceContext(start, cell, left))
        runtime.ledger.bump("parametric_width_forest_visits")
        if index + 1 < len(forest):
            left = _transfer(runtime, action, cell, left, 0)
    counter = "parametric_width_contexts_peak"
    runtime.ledger.bump(
        counter, max(0, len(contexts) - runtime.ledger.counters.get(counter, 0))
    )
    for _, cell in reversed(
        runtime.cells.source_span(maxwidth, source.length - maxwidth)
    ):
        right = _transfer(runtime, action, cell, right, 1)
    for context in reversed(contexts):
        start, cell, left = context.start, context.cell, context.left
        runtime.ledger.bump("parametric_width_parent_visits")
        if not _active(runtime, action, observer, cell, left, right, incoming):
            right = _transfer(runtime, action, cell, right, 1)
            continue
        while runtime.cells.node(cell).level:
            low, high = runtime.cells.split(cell)
            middle = start + runtime.cells.node(low).width
            middle_left = _transfer(runtime, action, low, left, 0)
            runtime.ledger.bump("parametric_width_descent_steps")
            if _active(runtime, action, observer, high, middle_left, right, incoming):
                start, cell, left = middle, high, middle_left
            else:
                right = _transfer(runtime, action, high, right, 1)
                cell = low
        return int(start + 1)
    return 0


__all__ = ["parametric_point", "parametric_width"]
