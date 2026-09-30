"""Public primitive routes use canonical tiles, including explicit lowering."""

from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_runtime import oracle


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("retired execution or scalar endpoint replay")


@pytest.mark.parametrize(
    ("effect", "source"),
    [
        (BaseBlockEffect(2), (1, 2, 1)),
        (BaseBlockEffect(10), (7, 18, 7)),
        (CollatzPhysicalBlockEffect(), (1, 1, 0, 1, 1)),
        (CollatzPhysicalBlockEffect(), (0, 0, 1, 1, 1)),
    ],
)
def test_public_primitive_square_fuses_points_and_width_without_midpoint(
    monkeypatch: pytest.MonkeyPatch,
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    source: tuple[int, int, int, int, int] | tuple[int, int, int],
) -> None:
    import number_compiler.hashlife.execution.tile_temporal as temporal
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        HigherSummaryArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimeValueArena,
    )

    compiler = LazyCompiler(ResourceLedger())
    primitive = compiler.atom(effect)
    square = compiler.compose(primitive, primitive)
    expected = tuple(oracle(effect, source, 16, 2))
    extent = max(
        (i + 1 for i, value in enumerate(expected) if value != effect.blank), default=0
    )
    index = HashLifeBlockIndex(square, source, logical_length=16)
    assert type(index._lazy_application) is LazyProjection
    source_tiles = index._ledger.counters.get("tile_publications", 0)
    with monkeypatch.context() as poison:
        poison.setattr(temporal, "complete_temporal", _forbidden)
        poison.setattr(TileArena, "join", _forbidden)
        poison.setattr(DiamondApplication, "point", _forbidden)
        poison.setattr(DiamondApplication, "active_width", _forbidden)
        poison.setattr(RuntimeValueArena, "action_function", _forbidden)
        poison.setattr(HigherSummaryArena, "runtime_unary", _forbidden)
        for coordinate in (0, extent // 2, extent - 1, 15):
            assert index.direct_powered_point(coordinate) == expected[coordinate]
        assert index.direct_active_width() == extent
    metrics = index.metrics()
    assert metrics.fused_interface_entries > 0
    assert metrics.tile_fused_observation_descents > 0
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0
    assert index._ledger.counters.get("tile_publications", 0) == source_tiles
    # Explicit lowering may now request complete canonical outputs. Its root
    # is retained across subsequent observations, including unseen positions.
    assert tuple(index.iter_direct_active()) == expected[:extent]
    monkeypatch.setattr(TileScheduler, "complete", _forbidden)
    monkeypatch.setattr(TileScheduler, "point", _forbidden)
    monkeypatch.setattr(TileScheduler, "width", _forbidden)
    assert index.direct_powered_point(1) == expected[1]
    assert index.direct_active_width() == extent


def test_public_reverse_terminal_pair_fuses_without_midpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_temporal as temporal

    pair = BaseBlockEffect(10)
    terminal = DigitNormalizeBlockEffect(10)
    compiler = LazyCompiler(ResourceLedger())
    composed = compiler.compose(compiler.atom(pair), compiler.atom(terminal))
    source = (7, 18, 7)
    midpoint = oracle(pair, source, 8, 1)
    expected = tuple(oracle(terminal, midpoint, 8, 1))
    extent = max(
        (index + 1 for index, value in enumerate(expected) if value != pair.blank),
        default=0,
    )
    index = HashLifeBlockIndex(composed, source, logical_length=8)
    assert type(index._lazy_application) is LazyProjection
    source_tiles = index._ledger.counters.get("tile_publications", 0)

    with monkeypatch.context() as poison:
        poison.setattr(temporal, "complete_temporal", _forbidden)
        poison.setattr(TileArena, "join", _forbidden)
        for coordinate, value in enumerate(expected):
            assert index.direct_powered_point(coordinate) == value
        assert index.direct_active_width() == extent

    assert index._ledger.counters.get("tile_publications", 0) == source_tiles
    assert index._ledger.counters["powered_absorption_successes"] == len(expected) + 1
    assert index.metrics().resource_accounting_mismatch == 0


@pytest.mark.parametrize(
    ("effect", "source"),
    [
        (BaseBlockEffect(2), (1, 2, 1)),
        (BaseBlockEffect(10), (7, 12, 7)),
        (CollatzPhysicalBlockEffect(), (1, 0, 1, 1)),
    ],
)
def test_public_primitive_point_width_and_endpoint_use_tile_executor(
    monkeypatch: pytest.MonkeyPatch,
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    source: tuple[int, int, int, int] | tuple[int, int, int],
) -> None:
    expected = tuple(oracle(effect, source, 8, 1))
    extent = max(i + 1 for i, value in enumerate(expected) if value != effect.blank)
    index = HashLifeBlockIndex(effect, source, logical_length=8)
    assert type(index._lazy_application) is LazyProjection
    monkeypatch.setattr(DiamondApplication, "point", _forbidden)
    monkeypatch.setattr(DiamondApplication, "active_width", _forbidden)
    assert index.direct_powered_point(0) == expected[0]
    assert index.direct_active_width() == extent
    monkeypatch.setattr(HashLifeBlockIndex, "direct_powered_point", _forbidden)
    monkeypatch.setattr(TileArena, "point", _forbidden)
    assert tuple(index.iter_direct_active()) == expected[:extent]
    assert index._ledger.counters["tile_endpoint_emissions"] == extent
    assert index._ledger.counters["explicitly_lowered_digits"] == extent


def test_public_completed_root_bypasses_constructors_and_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    index = HashLifeBlockIndex(BaseBlockEffect(2), (1, 2, 1), logical_length=8)
    expected = tuple(index.iter_direct_active())
    application = index._lazy_application
    assert type(application) is LazyProjection
    before = application.scheduler.ledger.counters.copy()
    monkeypatch.setattr(TileScheduler, "point", _forbidden)
    monkeypatch.setattr(TileScheduler, "width", _forbidden)
    monkeypatch.setattr(TileScheduler, "complete", _forbidden)
    monkeypatch.setattr(TileArena, "leaf", _forbidden)
    monkeypatch.setattr(TileArena, "join", _forbidden)
    # Clear the response register by observing a previously unqueried point.
    assert index.direct_powered_point(len(expected) - 1) == expected[-1]
    assert index.direct_active_width() == len(expected)
    assert application.scheduler.ledger.counters.get(
        "source_leaf_reads", 0
    ) == before.get("source_leaf_reads", 0)
    assert application.scheduler.ledger.counters.get(
        "tile_scheduler_frames", 0
    ) == before.get("tile_scheduler_frames", 0)


def test_public_metrics_forward_canonical_tile_runtime_inventory() -> None:
    index = HashLifeBlockIndex(BaseBlockEffect(2), (1, 2, 1), logical_length=8)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    index.direct_powered_point(0)
    index.direct_active_width()
    tuple(index.iter_direct_active())
    metrics = index.metrics()
    assert metrics.bounded_application_enabled == 1
    assert metrics.canonical_tile_nodes > 0
    assert metrics.canonical_tile_arena_nodes == metrics.canonical_tile_nodes
    assert metrics.canonical_tile_arena_nodes == (
        metrics.canonical_tile_arena_nodes_index_build
        + metrics.canonical_tile_arena_nodes_query
    )
    assert metrics.spacetime_macro_cache_entries == metrics.completed_result_entries > 0
    assert (
        metrics.spacetime_boundary_advance_cache_entries
        == metrics.powered_interface_entries
        > 0
    )
    assert (
        metrics.spacetime_tile_advance_cache_entries
        == metrics.spatial_interface_composition_entries
        > 0
    )
    assert (
        metrics.spacetime_tile_advance_cache_hits
        == metrics.spatial_interface_composition_early_hits
    )
    assert metrics.spacetime_tile_advance_cache_misses == (
        metrics.spatial_interface_composition_requests
        - metrics.spatial_interface_composition_early_hits
    )
    assert (
        metrics.bounded_application_temporal_state_classes
        == metrics.local_interface_nodes
        > 0
    )
    assert (
        metrics.bounded_application_temporal_action_classes
        == metrics.field_action_nodes
        > 0
    )
    assert (
        metrics.temporal_leaf_applications
        == metrics.tile_scheduler_leaf_function_applications
        > 0
    )
    assert metrics.bounded_application_query_requests == 2
    classified_execution_entries = (
        metrics.completed_result_entries
        + metrics.powered_interface_entries
        + metrics.spatial_interface_composition_entries
        + metrics.fused_interface_entries
        + metrics.normalized_region_entries
    )
    # The shared result memo also owns bounded observations such as directed
    # transfers, threshold summaries, and source-root matches.  The public
    # total must include, rather than erase, those independently validated
    # records.
    assert metrics.tile_execution_memo_entries >= classified_execution_entries
    assert metrics.tile_execution_memo_entries == len(
        projection.scheduler.results._memo
    )
    assert metrics.finite_action_retained_entries == (
        metrics.canonical_transfer_nodes
        + metrics.powered_interface_entries
        + metrics.spatial_interface_composition_entries
        + metrics.fused_interface_entries
    )
    assert metrics.finite_action_alias_hits == (
        metrics.resource_work_counters.get("quotient_semantic_interner_hits", 0)
    )
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0


def test_application_rejects_other_request_root_before_warm_hit() -> None:
    index = HashLifeBlockIndex(BaseBlockEffect(2), (1, 2, 1), logical_length=8)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    application = projection._application
    application.complete()
    scheduler = projection.scheduler
    source = scheduler.tiles.leaf(
        scheduler.tiles.resolve(application.source).alphabet, 0
    )
    other = scheduler.application(
        application.action, source.tile, application.ports, application.wiring
    )
    source.close()
    other.complete()
    original = application._root
    application._root = other._root
    before = scheduler.ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="another request"):
            application.point(0)
        with pytest.raises(ValueError, match="another request"):
            application.width()
        with pytest.raises(ValueError, match="another request"):
            application.close()
        assert scheduler.ledger.snapshot() == before
    finally:
        application._root = original
        other.close()
        projection.close()


@pytest.mark.parametrize("alias", [False, 0.0])
def test_warm_application_rejects_aliased_identity_before_mutation(
    alias: bool | float,
) -> None:
    index = HashLifeBlockIndex(BaseBlockEffect(2), (1, 2, 1), logical_length=8)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    application = projection._application
    application.complete()
    identity = application.identity
    object.__setattr__(application, "identity", alias)
    before = projection.ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="invalid scoped identity"):
            application.point(0)
        with pytest.raises(ValueError, match="invalid scoped identity"):
            application.close()
        assert projection.ledger.snapshot() == before
    finally:
        object.__setattr__(application, "identity", identity)
        projection.close()


def test_application_constructor_cannot_forge_scheduler_identity() -> None:
    index = HashLifeBlockIndex(BaseBlockEffect(2), (1, 2, 1), logical_length=8)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    application = projection._application
    assert_rejected_atomically(
        projection.ledger,
        lambda: TileApplication(
            projection.scheduler,
            application.identity,
            application.action,
            application.source,
            application.ports,
            application.wiring,
            None,
        ),
        TypeError,
        match="issued by their scheduler",
    )
