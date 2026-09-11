from __future__ import annotations

import gc
from pathlib import Path

from devtools.proofs.block_composed import ComposedBlockEffect
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicTile,
    join,
    leaf,
    mirror_tile,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_persistent_macro_key_retains_canonical_tile_identity() -> None:
    source = join(join(leaf(1), leaf(2)), join(leaf(3), leaf(4)))
    mirrored = mirror_tile(source)
    original_id = mirrored.node_id

    # Persistent macro keys retain canonical tile objects directly. The global
    # dyadic arena also owns them strongly, so construction-order IDs cannot churn.
    retained = {mirrored: "memo"}
    del mirrored
    gc.collect()

    rebuilt = mirror_tile(source)
    assert rebuilt.node_id == original_id
    assert retained[rebuilt] == "memo"


def test_recursive_carrier_bulk_and_leaf_traversal_share_one_state_identity() -> None:
    from devtools.proofs.block_power import power_block_effect

    effect = power_block_effect(base=10, exponent=8).root
    assert isinstance(effect, ComposedBlockEffect)
    start = effect.initial(BoundarySide.LEFT)
    blank = effect.blank
    values = (blank, 7, blank, blank)
    tile = join(
        join(leaf(values[0]), leaf(values[1])), join(leaf(values[2]), leaf(values[3]))
    )

    bulk = effect._advance_effect_tile_macro(effect, BoundarySide.LEFT, start, tile)
    scalar = start
    for symbol in values:
        scalar = effect.advance(BoundarySide.LEFT, scalar, symbol)
    assert bulk is scalar

    # Repeat at a deliberately non-aligned action-stream offset.  Alignment is
    # occurrence geometry; it must not manufacture a different residual ID.
    prefix_bulk = effect.advance(BoundarySide.LEFT, start, 5)
    shifted_bulk = effect._advance_effect_tile_macro(
        effect, BoundarySide.LEFT, prefix_bulk, tile
    )
    shifted_scalar = prefix_bulk
    for symbol in values:
        shifted_scalar = effect.advance(BoundarySide.LEFT, shifted_scalar, symbol)
    assert shifted_bulk is shifted_scalar


def test_lazy_range_hit_is_not_counted_on_computed_miss() -> None:
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    effect = BaseBlockEffect(10)
    index = HashLifeBlockIndex(effect, (7, 18, 7), logical_length=16)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    runtime = projection.scheduler
    application = projection._application
    request = (application.action, application.source, application.wiring)
    assert isinstance(runtime.adapter, PrimitiveTileKernelAdapter)
    first = runtime.adapter._compile_interface(*request)
    after_first = runtime.ledger.snapshot()
    assert after_first.counters["powered_interface_publications"] > 0
    assert runtime.adapter._compile_interface(*request) == first
    after_second = runtime.ledger.snapshot()
    assert (
        after_second.counters["powered_interface_early_hits"]
        == after_first.counters.get("powered_interface_early_hits", 0) + 1
    )
    assert (
        after_second.counters["powered_interface_publications"]
        == after_first.counters["powered_interface_publications"]
    )
    assert index.metrics().resource_accounting_mismatch == 0


def test_public_metrics_separate_bounded_production_from_generic_spacetime_caches() -> (
    None
):
    for term in (ReverseAddPoweredTerm(196, 32), PoweredCollatzTerm(27, 32)):
        term.digit(0)
        metrics = term.metrics()
        assert metrics.bounded_application_enabled == 1
        assert metrics.bounded_application_quotient_builds == (
            metrics.field_interface_publications
        )
        assert (
            metrics.bounded_application_temporal_state_classes
            == metrics.local_interface_nodes
            > 0
        )
        assert (
            metrics.bounded_application_temporal_action_classes
            == metrics.field_action_nodes
        )
        assert metrics.field_action_nodes > 0
        assert metrics.bounded_application_retained_entries > 0

        # Production reverse/add and Collatz no longer enter the generic
        # recursive occurrence/macro-cache carrier at all.  Those compatibility
        # families stay visible specifically so a regression is a nonzero value.
        family_entries = (
            metrics.spacetime_tile_advance_cache_entries
            + metrics.spacetime_boundary_advance_cache_entries
            + metrics.spacetime_reverse_boundary_advance_cache_entries
            + metrics.spacetime_tile_output_entries
            + metrics.spacetime_boundary_output_cache_entries
            + metrics.spacetime_sparse_transition_cache_entries
        )
        assert metrics.spacetime_macro_cache_entries == family_entries == 0
        assert metrics.spacetime_macro_cache_hits == 0
        assert metrics.spacetime_macro_cache_misses == 0
        assert metrics.scalar_emit_cache_entries == 0
        assert metrics.scalar_emit_cache_hits == 0
        assert metrics.scalar_emit_cache_misses == 0
        assert (
            metrics.retained_cache_entries
            >= metrics.bounded_application_retained_entries
        )


def test_lazy_production_retains_only_registered_scoped_programs_and_summaries() -> (
    None
):
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle

    term = ReverseAddPoweredTerm(196, 32)
    term.digit(0)
    index = term._point_index()
    assert not hasattr(index, "_advance_cache")
    metrics = index.metrics()
    assert metrics.resource_audit_complete == 1
    assert metrics.forbidden_future_payloads == 0
    assert metrics.resource_inventory
    assert all(
        item.observed_entries == item.entries for item in metrics.resource_inventory
    )
    assert all(
        isinstance(root, ArenaHandle)
        for item in metrics.resource_inventory
        for root in item.roots
    )


def test_unowned_global_source_tiles_are_reclaimable() -> None:
    import weakref

    symbols = (918273641, 918273642, 918273643, 918273644)
    tile = join(
        join(leaf(symbols[0]), leaf(symbols[1])),
        join(leaf(symbols[2]), leaf(symbols[3])),
    )
    old = weakref.ref(tile)
    del tile
    gc.collect()
    assert old() is None
    rebuilt = join(
        join(leaf(symbols[0]), leaf(symbols[1])),
        join(leaf(symbols[2]), leaf(symbols[3])),
    )
    assert rebuilt is not None
    assert rebuilt.left is not None
    assert rebuilt.right is not None
    assert rebuilt.left.left is not None
    assert rebuilt.right.right is not None
    assert (
        rebuilt.left.left.symbol == symbols[0]
        and rebuilt.right.right.symbol == symbols[3]
    )


def test_mirror_is_a_canonical_involutive_tile_action() -> None:
    tile = join(join(leaf(1), leaf(2)), join(leaf(3), leaf(4)))
    reflected = mirror_tile(tile)
    assert mirror_tile(tile) is reflected
    assert mirror_tile(reflected) is tile


def test_composed_hashlife_has_one_registered_owner_per_retained_container() -> None:
    for term in (ReverseAddPoweredTerm(196, 32), PoweredCollatzTerm(27, 32)):
        term.digit(0)
        index = term._point_index()
        assert not hasattr(index, "_advance_cache")
        inventory = index._ledger.inventory()
        assert len({item.owner for item in inventory}) == len(inventory)
        assert len({item.name for item in inventory}) == len(inventory)
        assert all(item.accounting_delta == 0 for item in inventory)
        assert term.metrics().bounded_application_retained_entries > 0


def test_collatz_compiler_syntax_is_separate_from_lazy_application_work() -> None:
    term = PoweredCollatzTerm(27, 32)
    before = term.metrics()
    term.digit(0)
    metrics = term.metrics()
    assert metrics.scalar_emit_compiler_probes == metrics.scalar_emit_cache_entries == 0
    assert metrics.compiler_symbolic_output_row_cache_entries == 0
    assert metrics.compiler_program_nodes > 0
    # Collatz's field action owns canonical symbolic affine/output programs in
    # the application arena.  They are production action syntax, not a copied
    # proof-state domain, and must be inventoried separately from compiler IR.
    assert metrics.application_program_nodes > 0
    assert metrics.action_program_nodes == (
        metrics.compiler_program_nodes + metrics.application_program_nodes
    )
    assert metrics.compiler_retained_execution_nodes == metrics.compiler_program_nodes
    assert before.point_queries == 0 and metrics.point_queries == 1


def test_public_compiler_never_constructs_cartesian_partition_domains() -> None:
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition

    for term in (PoweredCollatzTerm(27, 32), ReverseAddPoweredTerm(196, 32)):
        assert isinstance(term.effect, ProgramComposition)
        term.digit(0)
        metrics = term.metrics()
        assert (
            metrics.first_recursive_exponent_left
            == metrics.first_recursive_exponent_right
            == 0
        )
        assert (
            metrics.partition_carrier_layers_left
            == metrics.partition_carrier_layers_right
            == 0
        )
        assert (
            metrics.max_partition_domain_left == metrics.max_partition_domain_right == 0
        )
        assert metrics.compiler_program_nodes <= 4 * (32).bit_length()
        assert metrics.resource_audit_complete == 1


def test_lazy_carrier_metrics_expose_programs_without_duplicate_finite_domains() -> (
    None
):
    term = PoweredCollatzTerm(27, 32)
    term.digit(0)
    metrics = term.metrics()
    assert metrics.mixed_finite_carrier_layers == 0
    assert (
        metrics.functional_carrier_layers_left
        == metrics.partition_carrier_layers_left
        == 0
    )
    assert (
        metrics.recursive_carrier_layers_left
        == metrics.first_recursive_exponent_left
        == 0
    )
    assert (
        metrics.sparse_carrier_layers_left == metrics.sparse_carrier_layers_right == 0
    )
    assert (
        metrics.first_sparse_exponent_left == metrics.first_sparse_exponent_right == 0
    )
    assert metrics.max_partition_domain_left == 0
    assert metrics.compiler_program_nodes > 0 and metrics.application_program_nodes > 0
    assert metrics.action_program_nodes == (
        metrics.compiler_program_nodes + metrics.application_program_nodes
    )
    assert metrics.resource_audit_complete == 1
    assert metrics.retained_unbounded_future_integers == 0


def test_higher_carrier_has_no_eager_composed_universe_cutoff() -> None:
    import devtools.proofs.block_composed as composed

    text = Path(composed.__file__).read_text()
    assert "first.exponent) <= 8" not in text
    assert "max_states=4096" not in text
    from devtools.proofs.block_recursive import _RecursiveResidualAction
    from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect

    atom = BaseBlockEffect(3)
    effect = ComposedBlockEffect(
        atom, atom, budget=BlockContextBudget(), _force_recursive=True
    )
    assert all(
        isinstance(effect.initial(side), _RecursiveResidualAction)
        for side in BoundarySide
    )


def test_late_partition_alias_and_cache_compaction_paths_are_deleted() -> None:
    import devtools.proofs.block_partition as partition
    import devtools.proofs.block_spacetime_runtime as spacetime
    import number_compiler.arithmetic.contracts.block_effect as core

    partition_source = Path(partition.__file__).read_text()
    spacetime_source = Path(spacetime.__file__).read_text()
    core_source = Path(core.__file__).read_text()
    assert "refine_partition_behavioral_aliases" not in partition_source
    assert "canonical_representative" not in partition_source
    assert "_compact_canonical_state_caches" not in spacetime_source
    assert "effect_cache_owners" not in core_source
    assert "release_cache(" not in core_source

    import devtools.proofs.spacetime_boundary as boundary

    boundary_source = Path(boundary.__file__).read_text()
    assert "class SpacetimeBoundary" not in boundary_source
    assert "intern_boundary(" not in boundary_source


def test_retained_cache_accounting_matches_independently_observed_containers() -> None:
    for term in (ReverseAddPoweredTerm(196, 32), PoweredCollatzTerm(27, 32)):
        term.digit(0)
        metrics = term.metrics()
        assert metrics.raw_spacetime_boundary_cache_entries == 0
        assert metrics.retained_cache_accounting_delta == 0
        entries = tuple(item.observed_entries for item in metrics.resource_inventory)
        assert all(value is not None for value in entries)
        actual_entries = sum(value for value in entries if value is not None)
        actual_nodes = sum(
            item.observed_nodes or 0 for item in metrics.resource_inventory
        )
        assert (
            metrics.retained_cache_entries
            == metrics.budgeted_cache_entries
            == actual_entries
        )
        assert metrics.resource_ledger_nodes == actual_nodes
        assert (
            metrics.total_hashlife_retained_entries
            == metrics.cache_slots
            == actual_entries
        )
        assert (
            metrics.compiler_retained_cache_entries
            + metrics.query_retained_cache_entries
            + metrics.source_index_cache_entries
            == actual_entries
        )


def test_metrics_do_not_attribute_other_indices_work_to_an_existing_index() -> None:
    reverse = ReverseAddPoweredTerm(196, 32)
    reverse.digit(0)
    before = reverse.metrics()
    collatz = PoweredCollatzTerm(27, 32)
    collatz.digit(0)
    after, other = reverse.metrics(), collatz.metrics()
    for name in (
        "resource_ledger_entries",
        "resource_ledger_nodes",
        "resource_work_counters",
        "canonical_tile_arena_nodes_query",
        "canonical_tile_intern_misses_query",
        "compiler_program_nodes",
        "application_program_nodes",
    ):
        assert getattr(before, name) == getattr(after, name)
    assert other.canonical_tile_arena_nodes > 0
    assert other.canonical_tile_arena_nodes_query == 0
    assert other.compiler_retained_execution_nodes > 0
    assert other.query_retained_execution_nodes > 0
    assert other.resource_accounting_mismatch == 0
    assert other.resource_audit_complete == 1


def test_cold_miss_counters_match_new_entries_without_late_reinsertion() -> None:
    for term in (ReverseAddPoweredTerm(196, 64), PoweredCollatzTerm(27, 64)):
        term.digit(0)
        metrics = term.metrics()
        assert metrics.spacetime_tile_advance_repeated_cold_misses == 0
        assert metrics.spacetime_tile_output_repeated_cold_misses == 0
        assert metrics.scalar_emit_repeated_cold_misses == 0
        assert metrics.recursive_value_repeated_cold_misses == 0


def test_hashlife_tile_budget_counts_generated_quadtree_not_only_source_roots() -> None:
    import pytest

    from devtools.proofs.block_power import power_block_effect
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )

    power = power_block_effect(base=10, exponent=32)
    assert power.root is not None
    # The source fits, but the complete finite kernel and executable actions
    # share the same node budget. Rejection may occur during kernel admission,
    # before a query, and must not wait for a future exact-tree allocation.
    with pytest.raises(BlockContextBudgetExceeded):
        index = HashLifeBlockIndex(
            power.root,
            (7, 18, 7),
            logical_length=35,
            max_tile_nodes=64,
        )
        index.direct_powered_point(0)


def test_core_hashlife_semantics_do_not_trust_construction_order_tile_ids() -> None:
    from devtools.proofs.block_power import power_block_effect
    from devtools.proofs.spacetime_boundary import tile_uniform_symbol
    from devtools.proofs.finite_tile_action import (
        FiniteTileActionArena,
    )

    # Deliberately manufacture non-interned tiles with colliding diagnostic IDs.
    # Core semantic caches/traversals must use canonical objects/structure rather
    # than silently treating node_id as semantic identity.
    left = DyadicTile(10_000_001, 0, symbol=1)
    right = DyadicTile(10_000_002, 0, symbol=2)
    other_left = DyadicTile(10_000_001, 0, symbol=3)
    other_right = DyadicTile(10_000_002, 0, symbol=4)
    first_parent = join(left, right)
    second_parent = join(other_left, other_right)
    assert first_parent is not second_parent
    assert first_parent.left is not None
    assert first_parent.right is not None
    assert (first_parent.left.symbol, first_parent.right.symbol) == (1, 2)
    assert second_parent.left is not None
    assert second_parent.right is not None
    assert (second_parent.left.symbol, second_parent.right.symbol) == (3, 4)

    # The uniform-symbol memo has the same adversarial property: two distinct
    # objects may carry the same diagnostic ID without sharing semantics.
    same_id_one = DyadicTile(10_000_003, 0, symbol=1)
    same_id_two = DyadicTile(10_000_003, 0, symbol=2)
    assert tile_uniform_symbol(same_id_one) == 1
    assert tile_uniform_symbol(same_id_two) == 2

    finite = power_block_effect(base=10, exponent=2).root
    assert isinstance(finite, FiniteBlockEffect)
    arena = FiniteTileActionArena(finite)
    mixed = DyadicTile(
        10_000_004,
        1,
        left=left,
        right=right,
    )
    start = finite.initial(BoundarySide.LEFT)
    expected = finite.advance(
        BoundarySide.LEFT,
        finite.advance(BoundarySide.LEFT, start, 1),
        2,
    )
    assert arena.apply(BoundarySide.LEFT, mixed, start) == expected

    same_id_left = DyadicTile(10_000_005, 0, symbol=1)
    same_id_right = DyadicTile(10_000_005, 0, symbol=2)
    colliding_children = DyadicTile(
        10_000_006, 1, left=same_id_left, right=same_id_right
    )
    assert arena.apply(BoundarySide.LEFT, colliding_children, start) == expected


def test_standalone_finite_tile_action_reuse_counts_real_hits() -> None:
    from devtools.proofs.block_power import power_block_effect
    from devtools.proofs.finite_tile_action import (
        FiniteTileActionArena,
    )

    effect = power_block_effect(base=10, exponent=2).root
    assert isinstance(effect, FiniteBlockEffect)
    arena = FiniteTileActionArena(effect)
    tile = join(join(leaf(7), leaf(18)), join(leaf(7), leaf(effect.blank)))
    assert effect is not None
    start = effect.initial(BoundarySide.LEFT)
    before = arena.metrics()[0]
    first = arena.apply(BoundarySide.LEFT, tile, start)
    after_first = arena.metrics()[0]
    second = arena.apply(BoundarySide.LEFT, tile, start)
    after_second = arena.metrics()[0]
    assert second == first
    assert after_first.tile_cache_hits == before.tile_cache_hits
    assert after_second.tile_cache_hits == after_first.tile_cache_hits + 1
    assert after_second.unique_actions == after_first.unique_actions


def test_identical_warm_point_query_creates_no_new_hashlife_cold_entries() -> None:
    for term in (ReverseAddPoweredTerm(196, 64), PoweredCollatzTerm(27, 64)):
        index = term._point_index()
        first_value = index.direct_powered_point(0)
        first = index.metrics()
        # A response-register hit is distinct from a HashLife parent hit. Clear
        # only that one scalar so this assertion exercises the engine itself.
        index._point_response.clear()
        second_value = index.direct_powered_point(0)
        second = index.metrics()

        assert second_value == first_value
        assert (
            second.bounded_application_query_requests
            == first.bounded_application_query_requests + 1
        )
        # The cold query publishes its bounded interfaces.  Clearing only the
        # scalar response must reuse those exact quotient nodes without
        # publishing another one.
        assert (
            second.bounded_application_quotient_builds
            == first.bounded_application_quotient_builds
        )
        assert (
            second.bounded_application_retained_entries
            == first.bounded_application_retained_entries
        )
        assert (
            second.bounded_application_primitive_step_evaluations
            == first.bounded_application_primitive_step_evaluations
        )
        assert (
            second.bounded_application_exact_spatial_occurrences
            == first.bounded_application_exact_spatial_occurrences
        )
        assert (
            second.bounded_application_symbolic_action_nodes
            == first.bounded_application_symbolic_action_nodes
        )
        assert (
            second.canonical_tile_intern_misses_query
            == first.canonical_tile_intern_misses_query
        )
        assert (
            second.spacetime_macro_cache_hits == first.spacetime_macro_cache_hits == 0
        )
        assert (
            second.spacetime_macro_cache_misses
            == first.spacetime_macro_cache_misses
            == 0
        )
        assert (
            second.spacetime_macro_cache_entries
            == first.spacetime_macro_cache_entries
            == 0
        )
        assert (
            second.recursive_value_cache_misses
            == first.recursive_value_cache_misses
            == 0
        )
        assert (
            second.recursive_value_cache_entries
            == first.recursive_value_cache_entries
            == 0
        )
