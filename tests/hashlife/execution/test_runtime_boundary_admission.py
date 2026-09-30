"""Adversarial admission checks for retained runtime functions."""

from __future__ import annotations

from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.field_images import SourceCellID
from number_compiler.hashlife.execution.continuations.higher_values import RuntimeAtom
import pytest

from number_compiler.hashlife.execution.continuations.higher_operations import (
    evaluate_operation,
)
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    UnaryTemporal,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherFunctionID,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeContextState,
    RuntimeSummaryFunction,
    RuntimeTransferredState,
)
from number_compiler.resources.higher_value_record_audit import (
    valid_runtime_value_record,
)
from tests.support.reverse_higher_runtime import _fixture


def test_runtime_function_rejects_foreign_numeric_and_stale_ids_before_mutation() -> (
    None
):
    _, primitive, semantics, _, _, _, _, _ = _fixture((7,))
    _, foreign_primitive, foreign, _, _, _, _, _ = _fixture((7,))
    foreign_sort = foreign.state_sort(foreign_primitive, 0)
    foreign_parameter = foreign.variable(foreign_sort, "foreign")
    foreign_function = foreign.function(foreign_parameter, foreign_parameter)
    local_sort = semantics.state_sort(primitive, 0)
    local_parameter = semantics.variable(local_sort, "local")
    local_function = semantics.function(local_parameter, local_parameter)
    aliased_function = HigherFunctionID(
        local_function.owner,
        local_function.kind,
        local_function.local_id,
    )
    object.__setattr__(aliased_function, "local_id", True)
    values = semantics.runtime_values
    values.function(local_function, -1)
    before = semantics.ledger.snapshot()

    for function, environment in (
        (foreign_function, -1),
        (aliased_function, -1),
        (local_function, True),
        (local_function, -2),
    ):
        with pytest.raises((TypeError, ValueError)):
            values.function(function, environment)

    after = semantics.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_runtime_value_records_enforce_unary_and_context_summary_sorts() -> None:
    actions, primitive, semantics, runtime, _, _, sources, _ = _fixture((7, 18))
    temporal = actions.compose(primitive, primitive)
    unary = runtime.summaries.runtime_unary(
        temporal,
        sources.intern(0, 0),
        0,
    )
    recipe = runtime.summaries.runtime_unary_record(unary).recipe
    assert isinstance(recipe, UnaryTemporal)
    context = recipe.context
    continuation = semantics.runtime_values.action_function(
        "constant",
        temporal,
        0,
        0,
        None,
        -1,
    )
    records = (
        RuntimeTransferredState(context, 0),
        RuntimeContextState(unary, 0, 0, 0, 0),
        RuntimeSummaryFunction(unary, context, 0, 0, continuation),
    )

    for record in records:
        with pytest.raises(ValueError):
            valid_runtime_value_record(semantics.runtime_values, semantics, record)
    with pytest.raises(ValueError):
        semantics.runtime_values.transferred_state(context, 0)
    with pytest.raises(ValueError):
        semantics.runtime_values.context_state(unary, 0, 0, 0, 0)


def _deferred(
    runtime: HigherBimachineRuntime,
    semantics: HigherSemanticArena,
    action: FieldCellActionID,
    source: SourceCellID,
) -> RuntimeAtom:
    incoming = evaluate_operation(semantics, "initial", action, 0, ())
    transfer = runtime.summaries.runtime_unary(action, source, 0)
    return runtime.summaries.transfer_value(transfer, incoming)


def test_action_continuation_accepts_only_a_deferred_state_of_its_exact_sort() -> None:
    actions, primitive, semantics, runtime, _, _, sources, _ = _fixture((7, 18))
    two = actions.compose(primitive, primitive)
    four = actions.compose(two, two)
    source = sources.intern(0, 0)
    deferred = _deferred(runtime, semantics, two, source)
    values = semantics.runtime_values

    continuation = values.action_function(
        "constant",
        four,
        0,
        deferred,
        None,
        -1,
    )
    assert valid_runtime_value_record(
        values,
        semantics,
        values.resolve(continuation),
    )

    wrong = actions.compose(primitive, two)
    wrong_deferred = _deferred(runtime, semantics, wrong, source)
    before = semantics.ledger.snapshot()
    with pytest.raises(ValueError, match="another boundary sort"):
        values.action_function("constant", four, 0, wrong_deferred, None, -1)
    after = semantics.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_reverse_pair_symbols_use_the_complete_contiguous_alphabet() -> None:
    actions, primitive, semantics, _, _, _, _, _ = _fixture((7, 18))
    temporal = actions.compose(primitive, primitive)
    values = semantics.runtime_values
    _base, blank = semantics.schema.alphabet(temporal)
    assert blank == 19
    constant = values.action_function(
        "constant",
        temporal,
        0,
        0,
        None,
        -1,
    )
    step = values.action_function(
        "step",
        temporal,
        0,
        0,
        constant,
        blank - 1,
    )
    record = values.resolve(step)
    assert type(record) is RuntimeActionFunction
    assert valid_runtime_value_record(values, semantics, record)
    before = semantics.ledger.snapshot()

    with pytest.raises(ValueError, match="invalid input metadata"):
        values.action_function(
            "step",
            temporal,
            0,
            0,
            constant,
            blank + 1,
        )

    after = semantics.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert not valid_runtime_value_record(
        values,
        semantics,
        RuntimeActionFunction(
            "step",
            temporal,
            0,
            0,
            constant,
            blank + 1,
        ),
    )


def test_cyclic_runtime_pair_anchor_rejects_without_mutation() -> None:
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimePair,
        RuntimeValueID,
    )

    actions, primitive, semantics, _, _, _, _, _ = _fixture((7,))
    two = actions.compose(primitive, primitive)
    four = actions.compose(two, two)
    state = evaluate_operation(semantics, "initial", four, 0, ())
    assert type(state) is RuntimeValueID
    values = semantics.runtime_values
    pair = values.resolve(state)
    assert type(pair) is RuntimePair
    anchor = pair.anchor
    object.__setattr__(pair, "anchor", state)
    before = semantics.ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="cyclic anchor"):
            values._validate_action_atom(four, 0, state)
        assert semantics.ledger.snapshot() == before
    finally:
        object.__setattr__(pair, "anchor", anchor)
