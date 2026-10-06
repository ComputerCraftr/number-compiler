"""Capped diagnostics for actual diamond dependencies, not compiler node counts."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from time import perf_counter
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
)
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Evaluate,
    Initial,
    Output,
    OutputFunction,
    PairSummary,
    ResetTransfer,
    SpatialSummary,
    Substitute,
    Task,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryStateID
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.compilation import (
    compile_physical_diamond,
)

if TYPE_CHECKING:
    import typing

    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        LowerFinite,
        ResolveExpr,
    )
    from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
        HigherEmit,
        HigherInitial,
        HigherObserve,
        HigherStep,
        HigherSummary,
        HigherUnaryObserve,
        HigherUnarySummary,
    )
    from number_compiler.hashlife.execution.diamond_continuation_reduction import (
        CompilePrimitiveFunction,
        NormalizePrimitiveLambda,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        CompileStructuredExpression,
        StructuredExpressionTask,
    )
    from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
        PrimitiveMacroKey,
        PrimitiveMacroObservation,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import StructureID


@dataclass(frozen=True)
class Shape:
    task: str
    action_steps: int = 0
    provider_steps: int = 0
    level: int = -1
    side: int = -1
    continuation: str = ""


def shape(runtime: DiamondRuntime, task: Task) -> Shape:
    if isinstance(task, Initial):
        return Shape(
            "Initial", runtime.actions.node(task.action).exponent, side=task.side
        )
    if isinstance(task, (Transfer, ResetTransfer, Output)):
        return Shape(
            type(task).__name__,
            runtime.actions.node(task.action).exponent,
            runtime.actions.node(task.provider.action).exponent,
            runtime.cells.input_level(task.provider.cell),
            task.side if isinstance(task, (Transfer, ResetTransfer)) else -1,
        )
    if isinstance(task, Evaluate):
        function = runtime.boundaries.action(task.function)
        return Shape(
            "Evaluate",
            runtime.actions.node(
                runtime.boundaries.state(task.argument).action
            ).exponent,
            continuation=function.kind,
        )
    if isinstance(task, Substitute):
        step = task.step
        return Shape(
            "Substitute",
            runtime.actions.node(step.first).exponent
            + runtime.actions.node(step.second).exponent,
            runtime.actions.node(step.provider.action).exponent,
            runtime.cells.input_level(step.provider.cell),
            step.side,
            runtime.boundaries.action(step.previous).kind,
        )
    if isinstance(task, (PairSummary, SpatialSummary)):
        return Shape(
            type(task).__name__,
            runtime.actions.node(task.action).exponent,
            level=runtime.cells.node(task.cell).level,
            side=task.side if isinstance(task, SpatialSummary) else -1,
        )
    if isinstance(task, OutputFunction):
        return Shape("OutputFunction", runtime.actions.node(task.action).exponent)
    if isinstance(task, ContextObservation):
        return Shape("ContextObservation", side=task.side)
    return Shape(type(task).__name__)  # Newly added scheduler families remain visible.


def profile(
    steps: int, cap: int, source_bits: int = 11, *, width: bool = False
) -> dict[str, object]:
    ledger = ResourceLedger(max_cache_entries=cap)
    compiler = LazyCompiler(ledger)
    if source_bits < 1:
        raise ValueError("source bit count must be positive")
    bits = (1,) * source_bits
    extent = 523 if source_bits == 11 else source_bits + steps + 8
    source = SourceGeometry(
        ledger, ExactSource(bits, 2, blank=2, extent=extent, alphabet_size=2)
    )
    source.span(bits, 2, extent)
    runtime = DiamondRuntime(compiler, source)
    # Explicit primitive registration keeps the same source interface at zero.
    compiler.atom(CollatzPhysicalBlockEffect())
    root = compile_physical_diamond(compiler, runtime.actions, steps)
    application = DiamondApplication(runtime, root) if width else None
    calls: Counter[Shape] = Counter()
    original = runtime._program

    def program(
        task: Task,
    ) -> typing.Generator[
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
        | HigherInitial
        | HigherStep
        | HigherEmit
        | HigherSummary
        | HigherUnarySummary
        | HigherObserve
        | HigherUnaryObserve
        | LowerFinite
        | ResolveExpr
        | CompilePrimitiveFunction
        | NormalizePrimitiveLambda
        | CompileStructuredExpression
        | StructuredExpressionTask
        | PrimitiveMacroKey
        | PrimitiveMacroObservation,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
    ]:
        calls[shape(runtime, task)] += 1
        return original(task)

    object.__setattr__(runtime, "_program", program)
    start = perf_counter()
    digit: int | None = None
    active_width: int | None = None
    status = "complete"
    failed_phase: str | None = None
    phases: list[dict[str, object]] = []
    phase_start = perf_counter()
    try:
        digit = runtime.point(root, 0) if application is None else application.point(0)
    except BlockContextBudgetExceeded:
        status, failed_phase = "resource-cap", "point"
    phases.append(
        {
            "phase": "point",
            "status": status,
            "seconds": perf_counter() - phase_start,
            "value": digit,
            "entries": ledger.entries,
            "nodes": ledger.nodes,
            "work": dict(ledger.counters),
        }
    )
    if width:
        print(
            json.dumps(
                {
                    "completed_phase": "point",
                    "status": status,
                    "entries": ledger.entries,
                    "seconds": phases[-1]["seconds"],
                }
            ),
            file=sys.stderr,
            flush=True,
        )
    if status == "complete" and application is not None:
        phase_start = perf_counter()
        try:
            active_width = application.active_width()
        except BlockContextBudgetExceeded:
            status, failed_phase = "resource-cap", "width"
        phases.append(
            {
                "phase": "width",
                "status": status,
                "seconds": perf_counter() - phase_start,
                "value": active_width,
                "entries": ledger.entries,
                "nodes": ledger.nodes,
                "work": dict(ledger.counters),
            }
        )
    if width:
        print(
            json.dumps(
                {
                    "completed_phase": phases[-1]["phase"],
                    "status": status,
                    "entries": ledger.entries,
                    "seconds": phases[-1]["seconds"],
                }
            ),
            file=sys.stderr,
            flush=True,
        )
    elapsed = perf_counter() - start
    # Profiling closures are diagnostic workspace, not retained execution state.
    del runtime._program
    report = collect_ledger_metrics(ledger)
    state_shapes: Counter[tuple[int, str]] = Counter()
    for node in runtime.boundaries.states:
        continuation = (
            ""
            if node.continuation is None
            else runtime.boundaries.action(node.continuation).kind
        )
        state_shapes[runtime.actions.node(node.action).exponent, continuation] += 1
    assert all(type(value) is BoundaryStateID for value in runtime.transfers.values())
    return {
        "steps": steps,
        "source_bits": source_bits,
        "extent": extent,
        "cache_cap": cap,
        "status": status,
        "failed_phase": failed_phase,
        "digit": digit,
        "width": active_width,
        "seconds": elapsed,
        "phases": phases,
        "representation": {
            name: getattr(report, name)
            for name in (
                "representation_boundary_complete",
                "resource_audit_complete",
                "resource_accounting_mismatch",
                "forbidden_future_payloads",
                "resource_unregistered_containers",
            )
        },
        "entries": ledger.entries,
        "nodes": ledger.nodes,
        "work": ledger.counters,
        "cold_program_shapes": [
            dict(asdict(key), evaluations=value) for key, value in calls.most_common(30)
        ],
        "boundary_state_shapes": [
            {"steps": steps, "continuation": kind, "states": count}
            for (steps, kind), count in state_shapes.most_common()
        ],
    }


def _command() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, required=True)
    parser.add_argument("--cap", type=int, default=180000)
    parser.add_argument("--source-bits", type=int, default=11)
    parser.add_argument("--width", action="store_true")
    args = parser.parse_args()
    print(
        json.dumps(
            profile(args.steps, args.cap, args.source_bits, width=args.width),
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(_command))
