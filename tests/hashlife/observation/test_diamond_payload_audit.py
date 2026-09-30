"""Diamond schemas reject forged scopes and numeric histories under action roles."""

from __future__ import annotations

from copy import copy
from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken, ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.diamond_actions import (
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


@pytest.mark.parametrize(
    "effect",
    [
        BaseBlockEffect(3),
        DigitNormalizeBlockEffect(10),
        CollatzPhysicalBlockEffect(),
        NonblankBlockEffect(10, 19),
    ],
)
def test_actual_complete_kernel_domains_pass_without_changing_work(
    effect: BaseBlockEffect
    | CollatzPhysicalBlockEffect
    | DigitNormalizeBlockEffect
    | NonblankBlockEffect,
) -> None:
    arena = DiamondKernelArena()
    primitive = arena.intern(effect)
    expression = arena.constant(effect.blank + 1, 0)
    before = dict(arena.ledger.counters)
    registry = DiamondPayloadRegistry(arena.ledger)
    assert registry.valid(primitive)
    assert registry.valid(expression)
    metrics = collect_ledger_metrics(arena.ledger)
    assert metrics.representation_boundary_complete == 1
    assert metrics.finite_port_state_nodes == 1 + len(
        arena.kernel(primitive).left
    ) + len(arena.kernel(primitive).right)
    assert arena.ledger.counters == before


def test_foreign_and_unallocated_diamond_ids_are_not_semantic_payloads() -> None:
    arena = DiamondKernelArena()
    primitive = arena.intern(DigitNormalizeBlockEffect(10))
    expression = arena.constant(2, 0)
    registry = DiamondPayloadRegistry(arena.ledger)
    for handle in (primitive, expression):
        assert not registry.valid(replace(handle, owner=ArenaToken("foreign")))
        assert not registry.valid(replace(handle, local_id=1000000))
    node = arena.expression(expression)
    assert not registry.valid(
        replace(node, bits=(replace(node.bits[0], owner=ArenaToken("foreign")),))
    )


def test_unregistered_kernel_copy_cannot_confer_original_domain_authority() -> None:
    arena = DiamondKernelArena()
    primitive = arena.intern(CollatzPhysicalBlockEffect())
    original = arena.kernel(primitive)
    registry = DiamondPayloadRegistry(arena.ledger)
    assert not registry.valid(replace(original, left=tuple(original.left) * 100))
    assert not registry.domain(tuple(original.left) * 100)


def test_kernel_template_constants_are_bounded_by_actual_primitive_domains() -> None:
    from number_compiler.hashlife.interfaces.diamond_kernel import _KernelTemplateKey

    arena = DiamondKernelArena()
    kernel = arena.intern(DigitNormalizeBlockEffect(10))
    primitive = arena.kernel(kernel)
    registry = DiamondPayloadRegistry(arena.ledger)
    key = _KernelTemplateKey(kernel, "emit", 0, (None, 0, None))
    assert registry.valid(key)
    assert not registry.valid(replace(key, constants=(None, primitive.blank + 1, None)))
    assert not registry.valid(replace(key, constants=(None, 1 << 1000, None)))
    assert not registry.valid(replace(key, constants=(None, False, None)))
    assert not registry.valid(replace(key, constants=(None,)))


def test_temporal_images_retain_only_scoped_dag_metadata() -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compiler.atom(DigitNormalizeBlockEffect(10))
    actions = TemporalActionArena(compiler)
    action = actions.intern(effect)
    geometry = _geometry(ledger)
    cells = ImageCellArena(actions, geometry)
    image = cells.image(action, cells.source(0, 3))
    registry = DiamondPayloadRegistry(ledger)
    assert registry.valid(action) and registry.valid(image)
    assert registry.valid(cells.node(image))
    assert not registry.valid(replace(image, owner=ArenaToken("foreign")))
    assert not registry.valid(replace(cells.node(image), action=1000000))
    report = collect_ledger_metrics(ledger)
    assert report.representation_boundary_complete == 1
    assert report.diamond_cell_nodes + report.image_action_nodes == len(cells._nodes)
    assert report.image_action_nodes == 1
    assert report.temporal_program_nodes == len(compiler._nodes) + len(actions._nodes)


def test_complete_runtime_continuations_and_memo_keys_are_typed_payloads() -> None:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )

    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(DigitNormalizeBlockEffect(10))
    effect = compiler.compose(atom, atom)
    geometry = _geometry(ledger)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(effect)
    assert runtime.point(action, 1) == 3
    before = dict(ledger.counters)
    report = collect_ledger_metrics(ledger)
    assert report.representation_boundary_complete == 1
    assert report.canonical_transfer_nodes > 0
    assert report.image_program_cache_entries == len(runtime.macros) > 0
    assert report.canonical_parent_identity_entries == 0
    assert ledger.counters == before
    registry = DiamondPayloadRegistry(ledger)
    function = next(
        node for node in runtime.boundaries.actions if node.signature is not None
    )
    assert function.signature is not None
    assert registry.valid(function.signature)
    assert not registry.valid(replace(function.signature, input_size=1 << 63))
    with pytest.raises(ValueError, match="cardinality"):
        replace(function.signature, input_size=1 << 1000)
    constant = next(
        node for node in runtime.boundaries.actions if node.kind == "constant"
    )
    assert constant.signature is not None
    wrong_signature = replace(
        constant.signature, output_side=1 - constant.signature.output_side
    )
    assert registry.valid(wrong_signature)
    assert not registry.valid(replace(constant, signature=wrong_signature))


def test_composition_certification_requires_the_actual_registered_bound_record() -> (
    None
):
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )

    index = HashLifeBlockIndex(DigitNormalizeBlockEffect(10), (2,), logical_length=4)
    ledger = index._ledger
    report = index.metrics()
    assert (
        report.bimachine_composition_certified
        == report.representation_boundary_complete
        == 1
    )
    original = index._lazy_application
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    assert type(original) is LazyProjection
    index._lazy_application = copy(original)
    assert index.metrics().bimachine_composition_certified == 0
    index._lazy_application = original
    adapter = original.scheduler.adapter
    assert type(adapter) is PrimitiveTileKernelAdapter
    action = adapter._actions[original._application.action.local_id]
    owner = ledger.register("forged action certificate", "field_cell_action")
    records: LedgerList[object] = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(replace(action, kernel=replace(action.kernel, local_id=1 << 1000)))
    report = index.metrics()
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0


def test_parametric_macro_bindings_and_extensional_functions_have_distinct_units() -> (
    None
):
    from number_compiler.hashlife.tiles.tile_result_records import FusedInterfaceKey
    from tests.support.tile_kernel import _runtime, _tile

    ledger, tiles, adapter, first, scheduler = _runtime(BaseBlockEffect(2))
    second = adapter.admit(DigitNormalizeBlockEffect(2))
    pair = adapter.compose(first, second)
    with _tile(tiles, adapter, first, (1, 2, 1, 2)) as source:
        ports = adapter.initial_ports(first)
        wiring = adapter.wiring(pair)
        expected = adapter.fused_interface(
            pair, source.tile, ports, wiring, producer_wiring=adapter.wiring(first)
        )
        report = collect_ledger_metrics(ledger)
        assert report.representation_boundary_complete == 1
        assert (
            report.fused_interface_entries
            == sum(type(key) is FusedInterfaceKey for key in scheduler.results._memo)
            > 0
        )
        assert report.local_interface_nodes == len(adapter.quotients._nodes) > 0
        # Binding entries point to canonical semantic nodes; they are not
        # another population of interface functions or output images.
        assert report.image_program_cache_entries == 0
        assert report.spatial_binding_nodes == 0
        before = dict(ledger.counters)
        assert (
            adapter.fused_interface(
                pair, source.tile, ports, wiring, producer_wiring=adapter.wiring(first)
            )
            == expected
        )
        warm = collect_ledger_metrics(ledger)
        assert (
            ledger.counters.get("fused_interface_early_hits", 0)
            == before.get("fused_interface_early_hits", 0) + 1
        )
        assert warm.fused_interface_entries == report.fused_interface_entries
        assert warm.local_interface_nodes == report.local_interface_nodes
        assert warm.canonical_transfer_nodes == report.canonical_transfer_nodes


def test_projection_compatibility_fields_forward_actual_tile_work() -> None:
    import number_compiler.hashlife.observation.hashlife_projection as projection
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compiler.compose(
        compiler.atom(BaseBlockEffect(2)), compiler.atom(DigitNormalizeBlockEffect(2))
    )
    index = projection.HashLifeBlockIndex(
        effect, (1, 2, 1), logical_length=8, ledger=ledger, compiler=compiler
    )
    assert type(index._lazy_application) is LazyProjection
    index.direct_powered_point(0)
    report = index.metrics()
    assert (
        report.bimachine_composition_certified
        == report.representation_boundary_complete
        == 1
    )
    assert report.spacetime_macro_cache_entries == report.completed_result_entries
    assert (
        report.spacetime_tile_advance_cache_entries
        == report.spatial_interface_composition_entries
    )
    assert (
        report.spacetime_boundary_advance_cache_entries
        == report.powered_interface_entries
    )
    assert (
        report.temporal_leaf_applications
        == report.tile_scheduler_leaf_function_applications
    )
    # A fused point can complete its interface without constructing an output root.
    assert report.resource_work_counters["tile_fused_observation_requests"] > 0
    assert report.finite_action_unique == report.local_interface_nodes > 0
    assert report.finite_action_alias_hits == report.resource_work_counters.get(
        "quotient_semantic_interner_hits", 0
    )
    assert (
        report.bounded_application_temporal_state_classes
        == report.local_interface_nodes
        > 0
    )
    assert (
        report.bounded_application_temporal_action_classes == report.field_action_nodes
    )
    assert report.bounded_application_jump_entries == report.completed_result_entries
    assert (
        report.bounded_application_primitive_step_evaluations
        == report.sequential_generation_advances
        == 0
    )
    assert (
        report.bounded_application_nonlinear_branch_evaluations
        == report.primitive_transition_evaluations
    )
    assert (
        report.bounded_application_retained_entries
        == report.cache_slots - report.compiler_retained_cache_entries
    )
    behavior = index.behavior_metrics()
    assert behavior.temporal_quotient_family == "generic-tile-hashlife"
    assert behavior.temporal_description_nodes == report.temporal_program_nodes


def test_public_index_rejects_a_foreign_execution_backend(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.observation.hashlife_projection as projection
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    monkeypatch.setattr(
        projection, "build_bounded_application", lambda *_args, **_kwargs: object()
    )
    with pytest.raises(UnsupportedInterfaceError, match="canonical tile executor"):
        projection.HashLifeBlockIndex(BaseBlockEffect(2), (1, 2, 1), logical_length=8)


def _geometry(ledger: ResourceLedger) -> SourceGeometry:
    source = ExactSource((2, 3), 10, "reverse-add", 19, 8, alphabet_size=19)
    geometry = SourceGeometry(ledger, source)
    geometry.span(source.digits, 19, 8)
    return geometry
