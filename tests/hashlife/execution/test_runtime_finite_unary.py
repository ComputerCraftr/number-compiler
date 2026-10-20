"""Independent identity and composition checks for bounded runtime K actions."""

from __future__ import annotations

import importlib.util
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_operations import (
    evaluate_operation,
    force_value,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    HigherSummaryID,
    RuntimeUnarySummary,
    UnaryFinite,
    UnarySpatial,
    UnaryTemporal,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeFunction,
    RuntimeTableFunction,
)
from number_compiler.hashlife.execution.field_images import SourceCellArena
from number_compiler.resources.higher_value_record_audit import (
    valid_runtime_value_record,
)
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.reverse_higher_runtime import reverse_higher_fixture


def _two_unary_fixture() -> tuple[
    FieldCellActionID,
    HigherSemanticArena,
    HigherBimachineRuntime,
    SourceCellArena,
    HigherSummaryID,
    HigherSummaryID,
]:
    _, primitive, semantics, runtime, _, _, sources, _ = reverse_higher_fixture((0, 10))
    first = runtime.summaries.runtime_unary(primitive, sources.intern(0, 0), 1)
    second = runtime.summaries.runtime_unary(primitive, sources.intern(1, 0), 1)
    return primitive, semantics, runtime, sources, first, second


def _ordered_unary_fixture() -> tuple[
    FieldCellActionID,
    HigherSemanticArena,
    HigherBimachineRuntime,
    SourceCellArena,
    HigherSummaryID,
    HigherSummaryID,
    HigherSummaryID,
    HigherSummaryID,
]:
    fixture = _two_unary_fixture()
    runtime, first, second = fixture[2], fixture[4], fixture[5]
    forward = runtime.summaries.combine_runtime_unary((first, second))
    reverse = runtime.summaries.combine_runtime_unary((second, first))
    return (*fixture, forward, reverse)


def test_equal_complete_primitive_transfers_share_one_runtime_summary() -> None:
    _, primitive, _, runtime, _, _, sources, _ = reverse_higher_fixture((0, 1))
    first = runtime.summaries.runtime_unary(primitive, sources.intern(0, 0), 1)
    alias = runtime.summaries.runtime_unary(primitive, sources.intern(1, 0), 1)

    assert first == alias
    record = runtime.summaries.runtime_unary_record(first)
    assert isinstance(record.recipe, UnaryFinite)
    assert record.recipe.outputs == (1, 1, 4, 1, 4)
    assert len(runtime.summaries.audit_snapshot().runtime_bindings) == 2


def test_equal_observed_exit_does_not_alias_a_different_complete_transfer() -> None:
    _, primitive, _, runtime, _, _, sources, _ = reverse_higher_fixture((0, 9))
    constant = runtime.summaries.runtime_unary(primitive, sources.intern(0, 0), 1)
    identity = runtime.summaries.runtime_unary(primitive, sources.intern(1, 0), 1)
    constant_record = runtime.summaries.runtime_unary_record(constant)
    identity_record = runtime.summaries.runtime_unary_record(identity)

    assert constant != identity
    assert constant_record.recipe == UnaryFinite((1, 1, 4, 1, 4))
    assert identity_record.recipe.__class__.__name__ == "UnaryIdentity"
    assert (
        force_value(
            runtime.semantics,
            runtime.summaries.transfer_value(constant, 1),
        )
        == 1
    )
    assert (
        force_value(
            runtime.semantics,
            runtime.summaries.transfer_value(identity, 1),
        )
        == 1
    )
    assert (
        force_value(
            runtime.semantics,
            runtime.summaries.transfer_value(constant, 0),
        )
        == 1
    )
    assert (
        force_value(
            runtime.semantics,
            runtime.summaries.transfer_value(identity, 0),
        )
        == 0
    )


def test_runtime_spatial_composition_preserves_noncommuting_order() -> None:
    (
        _unused_primitive_binding,
        _unused_semantics_binding,
        runtime,
        _unused_sources_binding,
        constant_zero,
        constant_one,
        zero_then_one,
        one_then_zero,
    ) = _ordered_unary_fixture()
    assert zero_then_one != one_then_zero
    first = runtime.summaries.runtime_unary_record(constant_zero).recipe
    second = runtime.summaries.runtime_unary_record(constant_one).recipe
    assert isinstance(first, UnaryFinite) and isinstance(second, UnaryFinite)
    expected_forward = tuple(second.outputs[value] for value in first.outputs)
    expected_reverse = tuple(first.outputs[value] for value in second.outputs)
    assert expected_forward != expected_reverse
    assert (
        tuple(
            force_value(
                runtime.semantics,
                runtime.summaries.transfer_value(zero_then_one, incoming),
            )
            for incoming in range(len(first.outputs))
        )
        == expected_forward
    )
    assert (
        tuple(
            force_value(
                runtime.semantics,
                runtime.summaries.transfer_value(one_then_zero, incoming),
            )
            for incoming in range(len(first.outputs))
        )
        == expected_reverse
    )


@pytest.mark.parametrize("reverse", (False, True))
def test_normalized_finite_composition_matches_unreduced_spatial_semantics(
    reverse: bool,
) -> None:
    (
        primitive,
        _unused_semantics_binding,
        runtime,
        _unused_sources_binding,
        first,
        second,
    ) = _two_unary_fixture()
    if reverse:
        first, second = second, first
    normalized = runtime.summaries.combine_runtime_unary((first, second))
    baseline = runtime.summaries.intern_summary(
        RuntimeUnarySummary(
            primitive,
            1,
            UnarySpatial(first, second),
        )
    )

    assert normalized != baseline
    assert tuple(
        force_value(
            runtime.semantics,
            runtime.summaries.transfer_value(normalized, incoming),
        )
        for incoming in range(5)
    ) == tuple(
        force_value(
            runtime.semantics,
            runtime.summaries.transfer_value(baseline, incoming),
        )
        for incoming in range(5)
    )


@pytest.mark.parametrize("side", (0, 1))
def test_runtime_temporal_spatial_interchange_matches_unreduced_baseline(
    side: int,
) -> None:
    actions, primitive, semantics, runtime, _, _, sources, _ = reverse_higher_fixture(
        (7, 18)
    )
    temporal = actions.compose(primitive, primitive)
    first = runtime.summaries.runtime_unary(temporal, sources.intern(0, 0), side)
    second = runtime.summaries.runtime_unary(temporal, sources.intern(1, 0), side)
    normalized = runtime.summaries.combine_runtime_unary((first, second))
    baseline = runtime.summaries.intern_summary(
        RuntimeUnarySummary(
            temporal,
            side,
            UnarySpatial(first, second),
        )
    )
    incoming = evaluate_operation(semantics, "initial", temporal, side, ())
    samples = [incoming]
    for symbol in (0, 7, 18):
        samples.append(
            evaluate_operation(
                semantics,
                "step",
                temporal,
                side,
                (incoming, symbol),
            )
        )

    assert normalized != baseline
    assert [
        force_value(semantics, runtime.summaries.transfer_value(normalized, state))
        for state in samples
    ] == [
        force_value(semantics, runtime.summaries.transfer_value(baseline, state))
        for state in samples
    ]


def test_runtime_unary_rejects_numeric_foreign_and_wrong_side_aliases_atomically() -> (
    None
):
    _, primitive, semantics, runtime, _, _, sources, _ = reverse_higher_fixture((7, 9))
    left = runtime.summaries.runtime_unary(primitive, sources.intern(0, 0), 0)
    right = runtime.summaries.runtime_unary(primitive, sources.intern(0, 0), 1)
    _, foreign_action, _, foreign_runtime, _, _, foreign_sources, _ = (
        reverse_higher_fixture((7,))
    )
    foreign = foreign_runtime.summaries.runtime_unary(
        foreign_action,
        foreign_sources.intern(0, 0),
        0,
    )
    before = semantics.ledger.snapshot()

    with pytest.raises(ValueError):
        runtime.summaries.runtime_unary(primitive, sources.intern(0, 0), True)
    with pytest.raises((TypeError, ValueError)):
        runtime.summaries.combine_runtime_unary(
            cast(tuple[HigherSummaryID, ...], (left.local_id, left))
        )
    with pytest.raises(ValueError):
        runtime.summaries.combine_runtime_unary((left, foreign))
    with pytest.raises(ValueError):
        runtime.summaries.combine_runtime_unary((left, right))
    with pytest.raises(TypeError):
        runtime.summaries.transfer_value(left, True)

    after = semantics.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


@pytest.mark.parametrize("side", (0, 1))
def test_temporal_context_parent_and_binding_publish_atomically(side: int) -> None:
    actions, primitive, semantics, runtime, _, _, sources, _ = reverse_higher_fixture(
        (7, 18)
    )
    summaries = runtime.summaries
    temporal = actions.compose(primitive, primitive)
    first = summaries.runtime_unary(temporal, sources.intern(0, 0), side)
    second = summaries.runtime_unary(temporal, sources.intern(1, 0), side)
    a = summaries.runtime_unary_record(first).recipe
    b = summaries.runtime_unary_record(second).recipe
    assert isinstance(a, UnaryTemporal) and isinstance(b, UnaryTemporal)
    # Independently reusable child transfers are already published. Only the
    # associated parent context/node/binding are under test below.
    summaries.combine_runtime_unary((a.forward, b.forward))
    summaries.combine_runtime_unary((b.opposite, a.opposite))
    before = semantics.ledger.snapshot()
    snapshot = summaries.audit_snapshot()
    populations = (
        len(snapshot.nodes),
        len(snapshot.keys),
        len(snapshot.runtime_compositions),
    )
    semantics.ledger.max_cache_entries = before.entries + 4
    with pytest.raises(BlockContextBudgetExceeded):
        summaries.combine_runtime_unary((first, second))
    after = semantics.ledger.snapshot()
    assert (after.nodes, after.entries) == (before.nodes, before.entries)
    assert (
        len(summaries.audit_snapshot().nodes),
        len(summaries.audit_snapshot().keys),
        len(summaries.audit_snapshot().runtime_compositions),
    ) == populations
    assert (first, second) not in summaries.audit_snapshot().runtime_compositions
    semantics.ledger.max_cache_entries += 1
    parent = summaries.combine_runtime_unary((first, second))
    assert summaries.combine_runtime_unary((first, second)) == parent
    assert all(row.accounting_delta == 0 for row in semantics.ledger.inventory())


def test_primitive_tables_validate_exact_inputs_before_warm_lookup() -> None:
    actions, primitive, semantics, _, _, _, _, _ = reverse_higher_fixture((7,))
    tables = semantics.primitive_tables
    left_count = semantics.schema.state_count(primitive, 0)
    right_count = semantics.schema.state_count(primitive, 1)
    _base, blank = semantics.schema.alphabet(primitive)
    tables.step(primitive, 0, 0, 0)
    tables.emit(primitive, 0, 0, 0)
    composed = actions.compose(primitive, primitive)
    _foreign_actions, foreign, *_ = reverse_higher_fixture((7,))
    before = semantics.ledger.snapshot()

    for side, state, symbol in (
        (True, 0, 0),
        (0, True, 0),
        (0, 0, True),
        (0.0, 0, 0),
        (0, 0.0, 0),
        (0, 0, 0.0),
        (2, 0, 0),
        (0, left_count, 0),
        (1, right_count, 0),
        (0, 0, blank + 1),
    ):
        with pytest.raises((TypeError, ValueError)):
            tables.step(
                primitive,
                cast(int, side),
                cast(int, state),
                cast(int, symbol),
            )
    for left, symbol, right in (
        (True, 0, 0),
        (0, True, 0),
        (0, 0, True),
        (0.0, 0, 0),
        (0, 0.0, 0),
        (0, 0, 0.0),
        (left_count, 0, 0),
        (0, blank + 1, 0),
        (0, 0, right_count),
    ):
        with pytest.raises((TypeError, ValueError)):
            tables.emit(
                primitive,
                cast(int, left),
                cast(int, symbol),
                cast(int, right),
            )

    for action in (composed, foreign, primitive.local_id):
        with pytest.raises((TypeError, ValueError)):
            tables.step(cast(FieldCellActionID, action), 0, 0, 0)
        with pytest.raises((TypeError, ValueError)):
            tables.emit(cast(FieldCellActionID, action), 0, 0, 0)
    after = semantics.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_runtime_record_audit_rejects_numeric_aliases_and_incomplete_tables() -> None:
    actions, primitive, semantics, runtime, _, _, sources, _ = reverse_higher_fixture(
        (7,)
    )
    temporal = actions.compose(primitive, primitive)
    values = semantics.runtime_values
    domain = semantics.schema.state_count(primitive, 1)
    codomain = semantics.schema.state_count(primitive, 0)
    valid_outputs = tuple(range(domain))
    function = runtime.summaries.unary(
        primitive,
        sources.intern(0, 0),
        0,
    )
    semantic_function = runtime.summaries.unary_record(function).function

    assert valid_runtime_value_record(
        values,
        semantics,
        RuntimeTableFunction(temporal, 0, valid_outputs),
    )
    for record in (
        RuntimeFunction(semantic_function, True),
        RuntimeActionFunction("step", primitive, True, 0, None, 0),
        RuntimeActionFunction("step", primitive, 0, 0, None, True),
        RuntimeTableFunction(temporal, True, valid_outputs),
        RuntimeTableFunction(primitive, 0, valid_outputs),
        RuntimeTableFunction(temporal, 0, valid_outputs[:-1]),
        RuntimeTableFunction(temporal, 0, (*valid_outputs[:-1], codomain)),
        RuntimeTableFunction(temporal, 0, (*valid_outputs[:-1], True)),
    ):
        assert not valid_runtime_value_record(values, semantics, record)


@pytest.mark.parametrize(
    "outputs",
    ((0, True), (0, 2), [0, 0], tuple(range(65))),
)
def test_finite_unary_payload_rejects_boolean_wide_and_mutable_aliases(
    outputs: object,
) -> None:
    with pytest.raises(ValueError):
        UnaryFinite(cast(tuple[int, ...], outputs))


def test_production_collatz_shares_one_tile_execution_authority() -> None:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler

    assert (
        importlib.util.find_spec("number_compiler.sequences.collatz.concrete_port")
        is None
    )
    term = PoweredCollatzTerm(27, 8)
    assert term.digit(0) in (0, 1)
    workspace = term.source_image()
    scheduler = workspace.scheduler
    core = scheduler.source_image_core()
    assert scheduler.is_source_only
    assert core.audit_snapshot().adapters == {
        (workspace.family, workspace.semantic_version): workspace
    }
    view = core.view(workspace.root_image)
    assert view.binding.source == workspace.root_source
    assert view.binding.action == workspace.root_action
    assert scheduler.ledger is core.ledger is workspace.ledger is term.resource_ledger
    assert tuple(
        root
        for root in term.resource_ledger.iter_execution_roots()
        if type(root) is TileScheduler
    ) == (scheduler,)


def test_composition_inventory_rejects_wrong_same_interface_result() -> None:
    from number_compiler.resources.higher_payload_audit import audit_higher_payloads

    (
        _unused_primitive_binding,
        semantics,
        runtime,
        _unused_sources_binding,
        first,
        second,
        forward,
        reverse,
    ) = _ordered_unary_fixture()
    assert forward != reverse
    # This experimental reverse fixture is not an admitted production graph.
    # Check the retained generic summary owner, without whitelisting the fixture.
    clean = audit_higher_payloads(semantics.ledger)
    assert not clean.invalid
    summary_snapshot = runtime.summaries.audit_snapshot()
    runtime_compositions = cast(
        LedgerDict[tuple[HigherSummaryID, HigherSummaryID], HigherSummaryID],
        summary_snapshot.runtime_composition_store,
    )
    runtime_compositions[(first, second)] = reverse
    damaged = audit_higher_payloads(semantics.ledger)
    assert damaged.invalid


def test_temporal_leaf_publishes_complete_parent_for_warm_reuse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.experiments.reverse_add.temporal_leaf_diamond import (
        evaluate_temporal_leaf,
    )

    actions, primitive, semantics, *_ = reverse_higher_fixture()
    action = actions.compose(primitive, primitive)
    left = evaluate_operation(semantics, "initial", action, 0, ())
    right = evaluate_operation(semantics, "initial", action, 1, ())
    expected = evaluate_temporal_leaf(semantics, action, 7, left, right)
    assert semantics.ledger.counters["temporal_leaf_parent_publications"] > 0
    before = semantics.ledger.snapshot()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm semantic parent rebuilt its descendants")

    monkeypatch.setattr(semantics.schema, "children", forbidden)
    monkeypatch.setattr(
        "devtools.experiments.reverse_add.temporal_leaf_diamond.evaluate_operation",
        forbidden,
    )
    assert evaluate_temporal_leaf(semantics, action, 7, left, right) == expected
    after = semantics.ledger.snapshot()
    assert (before.nodes, before.entries) == (after.nodes, after.entries)
    assert after.counters["temporal_leaf_parent_hits"] > before.counters.get(
        "temporal_leaf_parent_hits",
        0,
    )
