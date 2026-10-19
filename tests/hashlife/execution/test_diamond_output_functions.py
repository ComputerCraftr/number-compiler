"""Finite output aliases must cover the whole kernel input alphabet."""

from __future__ import annotations

from dataclasses import fields, replace
from functools import partial
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    Output,
    OutputFunction,
)
from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def setup() -> tuple[DiamondRuntime, ActionProgramID, OutputFunction]:
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (0, 1), 4, 1
    )
    identity = runtime.actions.identity
    zero, one = (
        runtime.execute(Initial(identity, 0)),
        runtime.execute(Initial(identity, 1)),
    )
    left, right = (
        runtime.execute(Initial(action, 0)),
        runtime.execute(Initial(action, 1)),
    )
    request = OutputFunction(identity, zero, one, action, left, right)
    return runtime, action, request


def test_function_compilation_reads_no_source_and_warm_function_answers_all_symbols(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action, request = setup()
    primitive = runtime.kernel(action)
    left = runtime.boundaries.state(request.left).literal
    right = runtime.boundaries.state(request.right).literal
    expected = [primitive.emit(left, symbol, right) for symbol in range(3)]

    def forbidden(*args: object) -> Never:
        raise AssertionError("a function compiler observed an original/future cell")

    with monkeypatch.context() as patch:
        patch.setattr(runtime.cells, "input_symbol", forbidden)
        patch.setattr(runtime.cells, "source_symbol", forbidden)
        function = runtime.execute(request)
    assert type(function) is TransferSummaryID
    before = runtime.ledger.snapshot()
    with monkeypatch.context() as patch:
        patch.setattr(runtime.outputs, "compile", forbidden)
        assert runtime.execute(request) == function
    assert [
        runtime.outputs.observe(function, symbol) for symbol in range(3)
    ] == expected
    assert (
        runtime.ledger.entries == before.entries
        and runtime.ledger.nodes == before.nodes
    )


def test_different_cells_share_one_function_binding_without_retaining_observed_values() -> (
    None
):
    runtime, action, request = setup()
    function = runtime.execute(request)
    population = len(runtime.outputs.bindings)
    for position in (0, 1):
        cell = runtime.cells.source(position, 0)
        provider = ImageBinding(
            request.provider, cell, request.provider_left, request.provider_right
        )
        expected = runtime.outputs.observe(function, position)
        assert (
            runtime.execute(Output(provider, action, request.left, request.right))
            == expected
        )
    assert len(runtime.outputs.bindings) == population
    assert all(
        type(value) is TransferSummaryID for value in runtime.outputs.bindings.values()
    )
    assert {field.name for field in fields(request)} == {
        "provider",
        "provider_left",
        "provider_right",
        "action",
        "left",
        "right",
    }


def test_same_observed_value_does_not_alias_distinct_complete_functions() -> None:
    runtime, action, request = setup()
    functions = []
    for left in range(runtime.kernel(action).left_count):
        for right in range(runtime.kernel(action).right_count):
            key = replace(
                request,
                left=runtime.boundaries.literal(action, 0, left),
                right=runtime.boundaries.literal(action, 1, right),
            )
            function = runtime.execute(key)
            values = tuple(
                runtime.outputs.observe(function, symbol) for symbol in range(3)
            )
            functions.append((function, values))
    witnesses = [
        (a, b)
        for a in functions
        for b in functions
        if a[1][0] == b[1][0] and a[1] != b[1]
    ]
    assert witnesses
    assert all(a[0] != b[0] for a, b in witnesses)
    assert all(a[0] == b[0] for a in functions for b in functions if a[1] == b[1])


def test_foreign_and_nonprimitive_requests_reject_before_warm_lookup_or_mutation() -> (
    None
):
    runtime, action, request = setup()
    foreign, _, other = setup()
    runtime.execute(request)
    pair = runtime.actions.compose(action, action)
    left, right = runtime.execute(Initial(pair, 0)), runtime.execute(Initial(pair, 1))
    for invalid in (
        other,
        replace(request, left=other.left),
        replace(request, action=pair, left=left, right=right),
    ):
        assert_rejected_atomically(
            runtime.ledger, partial(runtime.execute, invalid), (TypeError, ValueError)
        )
    assert foreign.outputs.bindings == {}
