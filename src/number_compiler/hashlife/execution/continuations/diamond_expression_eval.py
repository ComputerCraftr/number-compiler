"""Transient scalar observations of closed finite boundary expressions.

This is a dependency program for the shared trampoline. Scalar output and
bound-state results are transient; complete finite functions remain reusable.
Only the requesting stack frame owns its at-most-three primitive arguments.
"""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import observation_inputs

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Result,
        Task,
    )


@dataclass(frozen=True, slots=True)
class LowerFinite:
    expression: ExprID


@dataclass(frozen=True, slots=True)
class ResolveExpr:
    """Expose one constructor, preserving unevaluated children of a state."""

    expression: ExprID


def resolve_expression(
    runtime: DiamondRuntime, task: ResolveExpr
) -> Generator[Task, Result, Result]:
    arena = runtime.higher.expressions
    node = arena.node(task.expression)
    if node.kind == "call":
        expanded = arena.expand_call(task.expression)
        return (yield ResolveExpr(expanded))
    if node.kind in ("anchor", "continuation"):
        parent = yield ResolveExpr(arena._handle(node.children[0]))
        if type(parent) is not ExprID:
            raise AssertionError("structured expression head returned a scalar")
        result = (
            arena.anchor(parent)
            if node.kind == "anchor"
            else arena.continuation(parent)
        )
        if result == task.expression:
            return result
        if node.kind == "continuation" and arena.node(result).kind == "lambda":
            from number_compiler.hashlife.execution.diamond_continuation_reduction import (
                NormalizePrimitiveLambda,
            )

            return (yield NormalizePrimitiveLambda(result))
        return (yield ResolveExpr(result))
    if node.kind == "apply":
        from number_compiler.hashlife.execution.diamond_continuation_reduction import (
            NormalizePrimitiveLambda,
        )

        function = yield ResolveExpr(arena._handle(node.children[0]))
        if type(function) is not ExprID:
            raise AssertionError("continuation head returned a scalar")
        function = yield NormalizePrimitiveLambda(function)
        if type(function) is not ExprID:
            raise AssertionError(
                "complete continuation normalization returned a scalar"
            )
        result = arena.apply(function, arena._handle(node.children[1]))
        if result == task.expression:
            return result
        return (yield ResolveExpr(result))
    return task.expression


def validate_finite_observation(runtime: DiamondRuntime, task: LowerFinite) -> None:
    node = runtime.higher.expressions.node(task.expression)
    if type(node.sort) is SymbolSort:
        return
    if (
        type(node.sort) is StateSort
        and runtime.actions.resolve(node.sort.action).kind != "compose"
    ):
        return
    raise ValueError("scalar observation requires a finite primitive result sort")


def lower_finite(
    runtime: DiamondRuntime, task: LowerFinite
) -> Generator[Task, Result, Result]:
    arena = runtime.higher.expressions
    resolved = yield ResolveExpr(task.expression)
    if type(resolved) is not ExprID:
        raise AssertionError("expression head returned a scalar")
    node = arena.node(resolved)
    runtime.ledger.bump("boundary_expression_scalar_observations")
    if node.kind == "symbol":
        return node.value
    if node.kind == "literal":
        return node.value
    if node.kind in ("finite_apply", "finite_map"):
        assert node.function is not None and type(node.sort) is StateSort
        result = yield LowerFinite(arena._handle(node.children[0]))
        if type(result) is not int:
            raise AssertionError("finite input was not a primitive state ordinal")
        input_sort = arena.nodes[node.children[0]].sort
        assert type(input_sort) is StateSort
        kernel = runtime.kernel(input_sort.action)
        domain = len(kernel.domain(BoundarySide(input_sort.side)))
        port = LEFT_A if input_sort.side == 0 else RIGHT_A
        return runtime.kernels.evaluate(
            node.function, observation_inputs(domain, port, result)
        )
    if node.kind not in ("advance", "emit") or node.action is None:
        raise ValueError("scalar observation contains an unresolved symbolic port")
    values: list[int | None] = [
        arena.nodes[child].value
        if arena.nodes[child].kind in ("literal", "symbol")
        else None
        for child in node.children
    ]
    if len(values) not in (2, 3):
        raise AssertionError(
            "a primitive operation exceeded its bounded argument interface"
        )
    runtime.kernel(node.action)
    kernel_id = runtime.primitive_ids[node.action]
    while True:
        constant = runtime.primitive_demand.constant(
            kernel_id,
            node.kind,
            node.side if node.kind == "advance" else 0,
            tuple(values),
        )
        if constant is not None:
            runtime.ledger.bump(
                "primitive_expression_arguments_elided", values.count(None)
            )
            return constant
        unresolved = [index for index, value in enumerate(values) if value is None]
        if not unresolved:
            raise AssertionError(
                "a completely bound primitive cofactor was not constant"
            )
        # Prefer an already finite transfer application over an unevaluated
        # temporal output. This changes demand order, never primitive semantics.
        index = min(
            unresolved,
            key=lambda i: (
                arena.nodes[node.children[i]].kind
                not in ("finite_apply", "finite_map", "advance"),
                i,
            ),
        )
        result = yield LowerFinite(arena._handle(node.children[index]))
        if type(result) is not int:
            raise AssertionError(
                "finite primitive dependency returned a structured value"
            )
        values[index] = result
        runtime.ledger.bump("primitive_expression_arguments_observed")
