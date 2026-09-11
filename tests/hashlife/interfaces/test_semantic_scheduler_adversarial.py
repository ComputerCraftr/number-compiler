"""Invalid shared semantic tasks reject before user payload protocols execute."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

import pytest

from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    CompileStructuredExpression,
    StructuredExpressionTask,
)
from tests.support.diamond_continuation_reduction import machine

if TYPE_CHECKING:
    import typing

    from number_compiler.arithmetic.functions.finite_function_types import FinitePort
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID


class _HashPayload:
    def __init__(self) -> None:
        self.calls = 0

    def __hash__(self) -> int:
        self.calls += 1
        return 0


def test_structured_parameter_admission_precedes_duplicate_hashing() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    parameter = arena.variable(arena.state_sort(action, 0), "input")
    payload = _HashPayload()
    before = runtime.ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        runtime.execute(
            CompileStructuredExpression(parameter, cast(tuple[ExprID, ...], (payload,)))
        )
    assert payload.calls == 0
    assert runtime.ledger.snapshot() == before


def test_structured_publication_admits_environment_before_unpacking_payload() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    parameter = arena.variable(arena.state_sort(action, 0), "input")
    compiler = runtime.semantic_compiler
    compiled = compiler.compile_structured(parameter, (parameter,))

    class IterablePayload:
        def __init__(self) -> None:
            self.calls = 0

        def __iter__(
            self,
        ) -> typing.Iterator[
            tuple[
                ExprID,
                FinitePort,
            ]
        ]:
            self.calls += 1
            return iter(((parameter, compiled.ports[0]),))

    payload = IterablePayload()
    malformed = StructuredExpressionTask(
        parameter, cast(tuple[tuple[ExprID, FinitePort], ...], payload)
    )
    before = runtime.ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        compiler.publication(malformed, compiled.structure)
    assert payload.calls == 0
    assert runtime.ledger.snapshot() == before
