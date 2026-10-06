"""Formal kernel constants and causal geometry never acquire future-tape authority."""

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    FormalSymbolID,
    ImageCellArena,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding
from number_compiler.hashlife.interfaces.diamond_halos import RightHalo
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_geometry_payloads import runtime


def test_formal_symbols_are_scoped_original_alphabet_constants_without_cells() -> None:
    engine, action = runtime()
    before = engine.ledger.snapshot()
    symbols = tuple(engine.cells.formal_symbol(i) for i in range(4))
    assert engine.ledger.snapshot() == before
    registry = DiamondPayloadRegistry(engine.ledger)
    assert all(registry.valid(symbol) for symbol in symbols)
    assert not registry.valid(
        FormalSymbolID(engine.cells.formal_token, "diamond-formal-symbol", 4)
    )
    assert not registry.valid(replace(symbols[0], owner=ArenaToken("foreign")))
    assert not registry.valid(
        CellID(engine.cells.formal_token, "diamond-formal-symbol", 0)
    )
    with pytest.raises(TypeError):
        engine.cells.resolve(cast("CellID", symbols[0]))
    left = engine.boundaries.literal(action, 0, 0)
    right = engine.boundaries.literal(action, 1, 0)
    provider = ImageBinding(action, symbols[2], left, right)
    registry = DiamondPayloadRegistry(engine.ledger)
    assert registry.valid(provider)
    other = ImageCellArena(engine.actions, engine.cells.source_geometry)
    other_symbol = other.formal_symbol(2)
    registry = DiamondPayloadRegistry(engine.ledger)
    assert registry.valid(other_symbol)
    assert not registry.valid(replace(provider, cell=other_symbol))
    assert collect_ledger_metrics(engine.ledger).representation_boundary_complete == 1


def test_halo_memo_is_owned_geometry_with_measured_warm_lookup() -> None:
    engine, atom = runtime()
    action = engine.actions.compose(atom, atom)
    assert engine.halos.right(action) == 0
    before = engine.ledger.snapshot()
    assert engine.halos.right(action) == 0
    after = engine.ledger.snapshot()
    assert after.entries == before.entries and after.nodes == before.nodes
    assert (
        after.counters["causal_halo_cache_hits"]
        == before.counters.get("causal_halo_cache_hits", 0) + 1
    )
    assert (
        after.counters["causal_halo_dag_visits"]
        == before.counters["causal_halo_dag_visits"]
    )
    assert (
        after.counters["causal_halo_requests"]
        == after.counters["causal_halo_cache_hits"]
        + after.counters["causal_halo_query_evaluations"]
    )
    before = engine.ledger.snapshot()
    report = collect_ledger_metrics(engine.ledger)
    assert engine.ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    assert report.causal_geometry_nodes == len(engine.halos._radii) > 0
    assert report.causal_geometry_nodes <= report.other_retained_nodes
    registry = DiamondPayloadRegistry(engine.ledger)
    actual = engine.halos._radii[action]
    assert registry.valid(actual)
    assert not registry.valid(replace(actual))
    engine.halos._radii[action] = RightHalo(action, 1 << 1000)
    report = collect_ledger_metrics(engine.ledger)
    assert report.representation_boundary_complete == 0
    assert report.forbidden_future_payloads > 0


def test_complete_output_function_keys_exclude_observations_and_validate_interfaces() -> (
    None
):
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Output,
        OutputFunction,
    )

    engine, action = runtime()
    left = engine.boundaries.literal(action, 0, 0)
    right = engine.boundaries.literal(action, 1, 0)
    identity = engine.actions.identity
    unit_left = engine.boundaries.literal(identity, 0, 0)
    unit_right = engine.boundaries.literal(identity, 1, 0)
    key = OutputFunction(identity, unit_left, unit_right, action, left, right)
    registry = DiamondPayloadRegistry(engine.ledger)
    assert registry.valid(key)
    assert not registry.valid(
        replace(key, provider=action, provider_left=left, provider_right=right)
    )
    assert not registry.valid(replace(key, left=right))
    assert not registry.valid(
        replace(key, provider=replace(action, owner=ArenaToken("foreign")))
    )
    different = engine.actions.intern(
        engine.actions.compiler.atom(DigitNormalizeBlockEffect(3))
    )
    different_left = engine.boundaries.literal(different, 0, 0)
    different_right = engine.boundaries.literal(different, 1, 0)
    registry = DiamondPayloadRegistry(engine.ledger)
    assert not registry.valid(
        replace(key, action=different, left=different_left, right=different_right)
    )
    provider = ImageBinding(action, engine.cells.formal_symbol(1), left, right)
    observation = Output(provider, action, left, right)
    assert not registry.valid(observation)
    assert engine.point(action, 0) == 1
    before = collect_ledger_metrics(engine.ledger)
    assert engine.point(action, 0) == 1
    after = collect_ledger_metrics(engine.ledger)
    assert after.representation_boundary_complete == 1
    assert after.output_function_cache_entries == len(engine.outputs.bindings) > 0
    assert after.output_function_cache_hits > before.output_function_cache_hits
    assert (
        after.primitive_transition_evaluations
        == before.primitive_transition_evaluations
    )
    assert after.primitive_output_evaluations == before.primitive_output_evaluations


def test_source_slice_and_certificate_construction_work_is_reported() -> None:
    from number_compiler.hashlife.execution.diamond_certificate import certify

    engine, atom = runtime()
    action = engine.actions.compose(atom, atom)
    certify(engine, action)
    assert engine.ledger.counters["diamond_certificate_construction_visits"] == 3
    assert engine.ledger.counters["diamond_certificate_construction_stack_peak"] == 2
    left, right = engine.cells.source(0, 1), engine.cells.source(2, 1)
    joined = engine.cells.join(right, left)
    engine.cells.slice(joined, 0, 0)
    assert engine.ledger.counters["diamond_slice_normalization_visits"] > 0
    engine.cells.source_span(0, 3)
    assert engine.ledger.counters["diamond_source_forest_chunks"] == 2
    assert engine.ledger.counters["diamond_source_forest_peak_chunks"] == 2
    assert_rejected_atomically(
        engine.ledger,
        lambda: engine.cells.slice(joined, 1, 1),
        ValueError,
        match="aligned",
    )


def test_bridge_admission_work_is_measured_only_after_successful_validation() -> None:
    from number_compiler.arithmetic.functions.finite_port_action import PortVariable
    from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
        from_expression,
        input_variable,
    )

    engine, action = runtime()
    arena = engine.boundaries
    port, expression = input_variable(arena, action, 0)
    signature = arena._signature(action, 0, action, 0)
    from_expression(arena, expression, signature, port)
    assert engine.ledger.counters["diamond_finite_bridge_admission_visits"] > 0
    assert engine.ledger.counters["diamond_finite_bridge_admission_stack_peak"] > 0
    assert engine.ledger.counters["diamond_finite_bridge_stack_peak_frames"] > 0
    assert engine.ledger.counters["diamond_finite_bridge_peak_result_entries"] > 0
    foreign = engine.kernels.variable(
        engine.kernels.expression(expression).domain, PortVariable(0, 0, "foreign", 0)
    )
    assert_rejected_atomically(
        engine.ledger,
        lambda: from_expression(arena, foreign, signature, port),
        ValueError,
        match="foreign finite input",
    )
