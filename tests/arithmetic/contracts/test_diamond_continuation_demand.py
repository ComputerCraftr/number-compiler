"""A constant continuation must not execute its discarded argument program."""

from __future__ import annotations

from collections.abc import Generator
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    Output,
    Result,
    Substitute,
    Task,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    ContinuationStep,
    ImageBinding,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_runtime import build, oracle

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def interfaces(
    runtime: DiamondRuntime,
    action: ActionProgramID,
) -> tuple[ActionProgramID, ActionProgramID, ImageBinding]:
    first = runtime.actions.reference(runtime.actions.node(action).first)
    second = runtime.actions.reference(runtime.actions.node(action).second)
    unit_left = runtime.execute(Initial(runtime.actions.identity, 0))
    unit_right = runtime.execute(Initial(runtime.actions.identity, 1))
    cell = runtime.cells.source_span(0, 1)[0][1]
    return (
        first,
        second,
        ImageBinding(runtime.actions.identity, cell, unit_left, unit_right),
    )


@pytest.mark.parametrize("side", [0, 1])
def test_constant_substitution_skips_the_opposite_transfer_before_any_execution(
    side: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime, action = build(CollatzPhysicalBlockEffect(), (1,), 8, 2)
    first, second, provider = interfaces(runtime, action)
    anchor = runtime.execute(Initial(first, side))
    argument = runtime.execute(Initial(first, 1 - side))
    target = runtime.execute(Initial(second, side))
    previous = runtime.boundaries.constant(target, first, 1 - side)
    step = ContinuationStep(first, second, side, previous, provider, anchor)
    discarded = Transfer(provider, first, argument, 1 - side)
    original = runtime._transfer

    def transfer(task: Transfer) -> Generator[Task, Result, Result]:
        if task == discarded:
            raise AssertionError("constant continuation scheduled a discarded argument")
        return (yield from original(task))

    monkeypatch.setattr(runtime, "_transfer", transfer)
    expected_symbol = runtime.kernel(first).emit(0, 1, 2)
    expected = runtime.kernel(second).advance(
        BoundarySide(side), runtime.boundaries.state(target).literal, expected_symbol
    )
    result = runtime.execute(Substitute(step, argument))
    assert runtime.boundaries.state(result).literal == expected
    assert runtime.ledger.counters["constant_continuation_argument_elisions"] >= 1
    assert discarded not in runtime.transfers


def test_two_constant_output_continuations_schedule_neither_argument(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = build(CollatzPhysicalBlockEffect(), (1,), 8, 2)
    first, second, provider = interfaces(runtime, action)
    left, right = (
        runtime.execute(Initial(action, 0)),
        runtime.execute(Initial(action, 1)),
    )

    def forbidden(*args: object) -> Never:
        raise AssertionError(
            "constant output continuations must not schedule a transfer"
        )

    monkeypatch.setattr(runtime, "_transfer", forbidden)
    expected = runtime.kernel(second).emit(0, runtime.kernel(first).emit(0, 1, 2), 2)
    assert runtime.execute(Output(provider, action, left, right)) == expected
    assert runtime.ledger.counters["constant_continuation_argument_elisions"] == 2


def test_nonconstant_contexts_remain_exact_after_demand_reduction() -> None:
    source = (1, 0, 1, 1, 0, 1)
    runtime, action = build(CollatzPhysicalBlockEffect(), source, 16, 8)
    expected = oracle(CollatzPhysicalBlockEffect(), source, 16, 8)
    assert [runtime.point(action, index) for index in (0, 1, 3, 6, 12, 15)] == [
        expected[index] for index in (0, 1, 3, 6, 12, 15)
    ]
    assert runtime.ledger.counters["constant_continuation_argument_elisions"] > 0


@pytest.mark.parametrize("provider_steps", [0, 2])
@pytest.mark.parametrize("fixed_output", [0, 1, 2])
def test_complete_primitive_constant_skips_all_source_and_provider_outputs(
    provider_steps: int, fixed_output: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime, composed = build(CollatzPhysicalBlockEffect(), (1,), 8, 2)
    atom = runtime.actions.reference(runtime.actions.node(composed).first)
    provider_action = runtime.actions.identity if not provider_steps else composed
    provider_left = runtime.execute(Initial(provider_action, 0))
    provider_right = runtime.execute(Initial(provider_action, 1))
    cell = runtime.cells.source_span(0, 1)[0][1]
    provider = ImageBinding(provider_action, cell, provider_left, provider_right)
    # EVEN mode copies only its right port, for all three possible symbols.
    left = runtime.boundaries.literal(atom, 0, 1)
    right = runtime.boundaries.literal(atom, 1, fixed_output)

    def forbidden(*args: object) -> Never:
        raise AssertionError(
            "constant primitive function forced its input source/provider"
        )

    monkeypatch.setattr(runtime.cells, "input_symbol", forbidden)
    original = runtime._raw_output

    def raw(task: Output) -> Generator[Task, Result, Result]:
        if task.action == composed:
            forbidden()
        return (yield from original(task))

    monkeypatch.setattr(runtime, "_raw_output", raw)
    assert runtime.execute(Output(provider, atom, left, right)) == fixed_output
    assert runtime.ledger.counters["primitive_output_provider_elisions"] == 1
    # Its canonical identity is the entire finite function, including nonzero
    # constants; no observed source symbol participated in this reduction.
    expression = next(iter(runtime.outputs.bindings.values()))
    assert runtime.outputs.constant(expression) == fixed_output


def test_nonconstant_primitive_function_still_observes_its_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, atom = build(CollatzPhysicalBlockEffect(), (1,), 8, 1)
    unit_left = runtime.execute(Initial(runtime.actions.identity, 0))
    unit_right = runtime.execute(Initial(runtime.actions.identity, 1))
    provider = ImageBinding(
        runtime.actions.identity,
        runtime.cells.source_span(0, 1)[0][1],
        unit_left,
        unit_right,
    )
    left, right = (
        runtime.boundaries.literal(atom, 0, 2),
        runtime.boundaries.literal(atom, 1, 0),
    )

    def forbidden(*args: object) -> Never:
        raise AssertionError("nonconstant output correctly requires its source")

    monkeypatch.setattr(runtime.cells, "input_symbol", forbidden)
    with pytest.raises(AssertionError, match="correctly requires"):
        runtime.execute(Output(provider, atom, left, right))
    assert runtime.ledger.counters.get("primitive_output_provider_elisions", 0) == 0
