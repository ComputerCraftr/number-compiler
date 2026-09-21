"""Distinguish syntactic programs, reduced functions, and work before aliasing."""

from dataclasses import replace
from types import SimpleNamespace

import pytest

from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.diamond_unary import UnaryComposition
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_registry import observed_node_partition
from tests.support.dataclass_records import replace_record
from tests.support.diamond_context_program import populated


def test_spatial_context_programs_are_not_counted_as_extensional_functions() -> None:
    runtime, _action, contexts, _request = populated()
    arena = runtime.pair_macros
    report = collect_ledger_metrics(runtime.ledger)
    assert report.representation_boundary_complete == 1
    assert report.spatial_action_program_nodes == len(contexts._nodes) + len(
        arena._nodes
    )
    assert report.context_program_nodes == len(contexts._nodes)
    assert report.macro_transfer_action_nodes == len(arena._nodes)
    assert len(contexts.observations) > 0
    assert len(contexts.unary._memo) > 0
    assert report.unary_function_cache_entries == len(contexts.unary._memo)
    inventory = {row.owner: row for row in report.resource_inventory}
    assert inventory[contexts.observations.owner].observed_entries == len(
        contexts.observations
    )
    assert inventory[contexts.unary.owner].observed_entries == len(contexts.unary._memo)
    assert report.boundary_substitution_cache_entries == len(runtime.continuations)
    partition = observed_node_partition(
        runtime.ledger.inventory(), dict(runtime.ledger.iter_containers())
    )
    assert sum(partition.values()) == report.resource_observed_nodes
    assert report.canonical_transfer_nodes == sum(
        row.observed_nodes or 0
        for row in report.resource_inventory
        if row.role in ("canonical_transfer", "finite_kernel_template")
    )
    assert not any(
        name.startswith("pair_macro_extensional_") for name in runtime.ledger.counters
    )
    key = next(iter(arena._bindings))
    expected = arena._bindings[key]
    before = runtime.ledger.snapshot()
    assert arena.cache_probe(key.action, key.cell) == expected
    after = runtime.ledger.snapshot()
    assert (
        after.counters["macro_transfer_cache_hits"]
        == before.counters.get("macro_transfer_cache_hits", 0) + 1
    )
    assert after.counters.get(
        "pair_macro_program_interner_hits", 0
    ) == before.counters.get("pair_macro_program_interner_hits", 0)
    assert arena._intern(arena.resolve(expected)) == expected
    assert (
        runtime.ledger.counters["pair_macro_program_interner_hits"]
        == after.counters.get("pair_macro_program_interner_hits", 0) + 1
    )


def test_unary_key_audit_checks_declared_variable_support_and_exact_port_type() -> None:
    runtime, _, contexts, _ = populated()
    key = next(key for key in contexts.unary._memo if type(key) is UnaryComposition)
    registry = DiamondPayloadRegistry(runtime.ledger)
    assert registry.valid(key)
    disguised = SimpleNamespace(
        time=0, side=key.port.side, bit=0, role=key.port.role, future=1 << 1000
    )
    assert not registry.valid(replace_record(key, {"port": disguised}))
    domain = runtime.kernels.expression(key.after).domain
    foreign = runtime.kernels.variable(domain, PortVariable(0, 0, "another-input", 0))
    registry = DiamondPayloadRegistry(runtime.ledger)
    assert not registry.valid(replace(key, after=foreign))


def test_early_unary_lookup_does_not_mask_late_expression_interning() -> None:
    runtime, _, contexts, _ = populated()
    key = next(key for key in contexts.unary._memo if type(key) is UnaryComposition)
    before = runtime.ledger.snapshot()
    contexts.unary.compose(key.kernel, key.side, key.before, key.after, key.port)
    after = runtime.ledger.snapshot()
    assert (
        after.counters["unary_function_composition_hits"]
        == before.counters.get("unary_function_composition_hits", 0) + 1
    )
    assert (
        after.counters["finite_expression_interner_requests"]
        == before.counters["finite_expression_interner_requests"]
    )
    runtime.kernels.constant(2, 0)
    before = runtime.ledger.snapshot()
    runtime.kernels.constant(2, 0)
    after = runtime.ledger.snapshot()
    assert (
        after.counters["finite_expression_interner_hits"]
        == before.counters["finite_expression_interner_hits"] + 1
    )
    assert (
        after.counters["finite_expression_component_checks"]
        == before.counters["finite_expression_component_checks"] + 1
    )


def test_repeated_finite_function_reduction_reports_late_alias_work() -> None:
    runtime, action, _, _ = populated()
    primitive = runtime.actions.reference(runtime.actions.node(action).first)
    arena = runtime.boundaries
    count = arena._domain_size(primitive, 0)
    assert count is not None
    values = [arena.literal(primitive, 0, 0)] * count
    expected = arena.finite_function(values, primitive, 0)
    before = runtime.ledger.snapshot()
    assert arena.finite_function(values, primitive, 0) == expected
    after = runtime.ledger.snapshot()
    assert after.entries == before.entries and after.nodes == before.nodes
    assert (
        after.counters["boundary_function_reduction_evaluations"]
        == before.counters["boundary_function_reduction_evaluations"] + 1
    )
    assert (
        after.counters["boundary_function_result_alias_hits"]
        == before.counters.get("boundary_function_result_alias_hits", 0) + 1
    )
    assert (
        after.counters["boundary_function_domain_visits"]
        == before.counters["boundary_function_domain_visits"] + count
    )
    assert (
        after.counters["boundary_function_pair_reductions"]
        > before.counters["boundary_function_pair_reductions"]
    )


def test_singleton_finite_domain_reports_live_workspace_without_reduction_loop() -> (
    None
):
    from tests.support.diamond_geometry_payloads import runtime

    engine, atom = runtime()
    arena = engine.boundaries
    value = arena.literal(atom, 0, 0)
    assert arena._domain_size(atom, 1) == 1
    arena.finite_function([value], atom, 1)
    # Output references, singleton frontier, staged-node list and staged map.
    assert engine.ledger.counters["boundary_function_workspace_peak"] == 4


def test_reset_certificates_are_distinct_from_output_halos_and_guard_state_free_keys() -> (
    None
):
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        ResetTransfer,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding
    from number_compiler.hashlife.interfaces.diamond_resets import (
        RightResetCertificates,
    )
    from tests.support.diamond_geometry_payloads import runtime

    engine, action = runtime()
    resets = RightResetCertificates(engine)
    assert resets.radius(action) == 0
    before = engine.ledger.snapshot()
    proof = resets.certificates[action]
    registry = DiamondPayloadRegistry(engine.ledger)
    assert registry.valid(proof)
    assert not registry.valid(replace(proof))
    with pytest.raises(ValueError, match="reset certificate"):
        replace(proof, law="output-halo")
    identity = engine.actions.identity
    left = engine.boundaries.literal(identity, 0, 0)
    right = engine.boundaries.literal(identity, 1, 0)
    provider = ImageBinding(identity, engine.cells.source(0, 1), left, right)
    request = ResetTransfer(provider, action, 1)
    registry = DiamondPayloadRegistry(engine.ledger)
    assert registry.valid(request)
    assert not registry.valid(replace(request, side=0))
    assert not registry.valid(replace(request, side=True))
    before = engine.ledger.snapshot()
    report = collect_ledger_metrics(engine.ledger)
    assert engine.ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    assert report.right_reset_certificate_nodes == len(resets.certificates)


def test_primitive_spatial_bindings_have_actual_slots_and_early_hit_units() -> None:
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        SpatialSummary,
    )
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
    from tests.support.diamond_runtime import build

    runtime, action = build(CollatzPhysicalBlockEffect(), (1, 1, 0, 1), 4, 1)
    request = SpatialSummary(action, runtime.cells.source(0, 2), 0)
    expected = runtime.execute(request)
    before = runtime.ledger.snapshot()
    assert runtime.execute(request) == expected
    after = runtime.ledger.snapshot()
    assert after.entries == before.entries and after.nodes == before.nodes
    assert (
        after.counters["primitive_spatial_requests"]
        == before.counters["primitive_spatial_requests"] + 1
    )
    assert (
        after.counters["primitive_spatial_cache_hits"]
        == before.counters.get("primitive_spatial_cache_hits", 0) + 1
    )
    assert (
        after.counters["primitive_spatial_evaluations"]
        == before.counters["primitive_spatial_evaluations"]
    )
    assert (
        after.counters["primitive_transition_evaluations"]
        == before.counters["primitive_transition_evaluations"]
    )
    report = collect_ledger_metrics(runtime.ledger)
    assert runtime.ledger.snapshot() == after
    assert report.representation_boundary_complete == 1
    assert report.primitive_spatial_cache_entries == len(runtime.spatial.bindings) > 0
    assert report.spatial_occurrence_bindings >= report.primitive_spatial_cache_entries
    assert DiamondPayloadRegistry(runtime.ledger).valid(request)


def test_warm_unary_composition_hits_before_repeated_admission_work() -> None:
    runtime, _, contexts, _ = populated()
    key = next(key for key in contexts.unary._memo if type(key) is UnaryComposition)
    contexts.unary.compose(key.kernel, key.side, key.before, key.after, key.port)
    before = runtime.ledger.snapshot()
    contexts.unary.compose(key.kernel, key.side, key.before, key.after, key.port)
    after = runtime.ledger.snapshot()
    popped = (
        after.counters["unary_function_admission_frame_visits"]
        - before.counters["unary_function_admission_frame_visits"]
    )
    unique = (
        after.counters["unary_function_admission_visits"]
        - before.counters["unary_function_admission_visits"]
    )
    assert popped == unique == 0
    assert after.counters[
        "unary_function_admission_workspace_peak"
    ] >= after.counters.get("unary_function_admission_unique_peak", 0)
    assert after.entries == before.entries and after.nodes == before.nodes
    same = runtime.kernels.constant(2, 0)
    before = runtime.ledger.snapshot()
    assert contexts._input_port((same, same, same)) is None
    after = runtime.ledger.snapshot()
    assert (
        after.counters["context_variable_support_frame_visits"]
        - before.counters["context_variable_support_frame_visits"]
        == 3
    )
    assert (
        after.counters["context_variable_support_visits"]
        - before.counters["context_variable_support_visits"]
        == 1
    )
    assert after.counters["context_variable_support_workspace_peak"] >= 3
    assert after.entries == before.entries and after.nodes == before.nodes


def test_spatial_source_admission_is_staged_and_warm_validation_work_is_visible() -> (
    None
):
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        SpatialSummary,
    )
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
    from tests.support.diamond_runtime import build

    runtime, action = build(CollatzPhysicalBlockEffect(), (1, 1, 0, 1), 4, 1)
    cell = runtime.cells.source(0, 2)
    before = runtime.ledger.snapshot()
    # The immutable original_forward proof is checked directly: one visit,
    # no pending stack or seen-set workspace is allocated.
    assert runtime.pair_macros._require_source(cell) == (1, 1, 0, 0)
    assert runtime.ledger.snapshot() == before
    task = SpatialSummary(action, cell, 0)
    runtime.execute(task)
    before = runtime.ledger.snapshot()
    runtime.execute(task)
    after = runtime.ledger.snapshot()
    assert (
        after.counters["spatial_source_admission_frame_visits"]
        > before.counters["spatial_source_admission_frame_visits"]
    )
    assert (
        after.counters["primitive_spatial_evaluations"]
        == before.counters["primitive_spatial_evaluations"]
    )
    assert after.counters["spatial_source_admission_workspace_peak"] == 0
    assert after.entries == before.entries and after.nodes == before.nodes


def test_original_source_reads_and_interner_reuse_have_distinct_units() -> None:
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    index = HashLifeBlockIndex(
        DigitNormalizeBlockEffect(2), (1, 2, 1), logical_length=4
    )
    geometry = index._source_geometry
    before = index.metrics()
    assert before.canonical_tile_arena_nodes > 0
    assert before.tile_observations == index._ledger.counters["source_leaf_reads"]
    assert geometry.read(0) == geometry.read(0) == 1
    observed = index.metrics()
    assert observed.tile_observations == before.tile_observations + 2
    assert observed.canonical_tile_arena_nodes == before.canonical_tile_arena_nodes
    slots = geometry.ledger.entries
    geometry.span((1, 2, 1), 3, 4)
    assert geometry.ledger.entries == slots
    counts = geometry.ledger.counters
    for prefix in ("source_leaf_interner", "source_parent_interner"):
        assert (
            counts[prefix + "_requests"]
            == counts.get(prefix + "_hits", 0) + counts[prefix + "_evaluations"]
        )
        assert counts[prefix + "_hits"] > 0
    assert index.metrics().tile_observations == before.tile_observations + 2
