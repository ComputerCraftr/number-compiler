"""Shared-scheduler construction requests for factored semantic expressions."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    ReachableCodec,
    SemanticProfileID,
)
from number_compiler.hashlife.interfaces.semantic_state_codec import StateCodec


@dataclass(frozen=True, slots=True)
class CompileStructuredExpression:
    expression: ExprID
    parameters: tuple[ExprID, ...] = ()
    profile: SemanticProfileID | None = None


@dataclass(frozen=True, slots=True)
class StructuredExpressionTask:
    expression: ExprID
    environment: tuple[tuple[ExprID, FinitePort | StateCodec | ReachableCodec], ...]
    depth: int = 0
    profile: SemanticProfileID | None = None


StructuredTask: TypeAlias = CompileStructuredExpression | StructuredExpressionTask
STRUCTURED_EXPRESSION_TASKS = (CompileStructuredExpression, StructuredExpressionTask)
