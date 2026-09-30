"""Persistent exact aliases for canonical causal-boundary concatenation."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.result_reverse_indexes import publish_indexed_result
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
    concat_boundary_views,
    normalize_boundary_view,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BoundaryConcatKey,
    BoundaryConcatResult,
    boundary_view_snapshot,
)
from number_compiler.hashlife.tiles.tile_result_validation import (
    validate_boundary_operands,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileAlphabetID, TileID, TileLease
from number_compiler.resources.result_cache_kinds import (
    record_unattributed_post_eviction_miss,
)

if TYPE_CHECKING:
    from number_compiler.resources.tile_dependency_leases import (
        DependencyLeaseBatch,
        TileDependencyLeases,
    )


def _view(view: BoundaryTileView) -> BoundaryTileView:
    """Detach occurrence scalars and omit the irrelevant exterior origin."""
    return BoundaryTileView(
        TileID(view.tile.owner, view.tile.kind, view.tile.local_id),
        0,
        view.relative_extent,
        view.orientation,
        view.source_offset,
    )


def _key(
    arena: CompletedResultArena,
    alphabet: TileAlphabetID,
    first: BoundaryTileView,
    second: BoundaryTileView,
) -> BoundaryConcatKey:
    candidate = BoundaryConcatKey(alphabet, first, second)
    _validate_key(arena, candidate)
    return BoundaryConcatKey(alphabet, _view(first), _view(second))


def _snapshot(
    key: BoundaryConcatKey,
    value: BoundaryConcatResult,
) -> tuple[object, ...]:
    return (
        type(key),
        (
            type(key.alphabet),
            key.alphabet.owner,
            key.alphabet.kind,
            key.alphabet.local_id,
        ),
        boundary_view_snapshot(key.first),
        boundary_view_snapshot(key.second),
        boundary_view_snapshot(value.view),
    )


def _validate_key(arena: CompletedResultArena, key: BoundaryConcatKey) -> None:
    if type(arena) is not CompletedResultArena:
        raise TypeError("boundary concatenation requires the shared result arena")
    if type(key) is not BoundaryConcatKey:
        raise TypeError("boundary concatenation has another key sort")
    if type(key.alphabet) is not TileAlphabetID:
        raise TypeError("boundary concatenation requires a scoped alphabet ID")
    arena.tiles.alphabet(key.alphabet)
    if (
        type(key.first) is not BoundaryTileView
        or type(key.second) is not BoundaryTileView
    ):
        raise TypeError("boundary concatenation requires two exact views")
    validate_boundary_operands(
        arena.tiles,
        BoundaryTileOperands(key.first, key.second),
        expected_alphabet=key.alphabet,
    )
    if not key.first.relative_extent or not key.second.relative_extent:
        raise ValueError("boundary concatenation requires two nonempty views")


def _validate_value(
    arena: CompletedResultArena,
    key: BoundaryConcatKey,
    value: BoundaryConcatResult,
    *,
    published: bool,
) -> None:
    if type(value) is not BoundaryConcatResult:
        raise TypeError("boundary concat memo contains another value sort")
    value.__post_init__()
    validate_boundary_operands(
        arena.tiles,
        BoundaryTileOperands(value.view),
        expected_alphabet=key.alphabet,
    )
    output = arena.tiles.resolve(value.view.tile)
    total = key.first.relative_extent + key.second.relative_extent
    if (
        value.view.relative_origin != 0
        or value.view.relative_extent != total
        or value.view.orientation != 0
        or value.view.source_offset != 0
        or output.width < total
    ):
        raise ValueError("boundary concatenation changed its logical geometry")
    if published:
        if value._publication_owner is not arena._interface_publication_seal:
            raise ValueError("boundary concat result was not issued by this arena")
        if value._publication_snapshot != _snapshot(key, value):
            raise ValueError("boundary concat publication metadata was modified")


def _sealed(
    arena: CompletedResultArena,
    key: BoundaryConcatKey,
    view: BoundaryTileView,
) -> BoundaryConcatResult:
    plain = BoundaryConcatResult(_view(view))
    return BoundaryConcatResult(
        plain.view,
        arena._interface_publication_seal,
        _snapshot(key, plain),
    )


def lookup_boundary_concat(
    arena: CompletedResultArena,
    key: BoundaryConcatKey,
) -> BoundaryConcatResult | None:
    """Probe a validated exact concat before traversing either operand."""
    if type(key) is not BoundaryConcatKey:
        raise TypeError("boundary concatenation has another key sort")
    canonical = _key(arena, key.alphabet, key.first, key.second)
    return _lookup_canonical(arena, canonical)


def _lookup_canonical(
    arena: CompletedResultArena,
    canonical: BoundaryConcatKey,
) -> BoundaryConcatResult | None:
    arena.ledger.bump("tile_boundary_concat_cache_requests")
    found = arena._memo.get(canonical)
    if found is None:
        arena.ledger.bump("tile_boundary_concat_cache_misses")
        record_unattributed_post_eviction_miss(arena.ledger, "region")
        return None
    if type(found) is not BoundaryConcatResult:
        raise TypeError("boundary concat memo contains another value sort")
    _validate_value(arena, canonical, found, published=True)
    arena.ledger.bump("tile_boundary_concat_cache_early_hits")
    return found


def _publish(
    arena: CompletedResultArena,
    key: BoundaryConcatKey,
    value: BoundaryConcatResult,
) -> tuple[BoundaryConcatResult, bool]:
    _validate_key(arena, key)
    _validate_value(arena, key, value, published=True)
    found = arena._memo.get(key)
    arena.ledger.bump("tile_boundary_concat_cache_publication_requests")
    if found is not None:
        if type(found) is not BoundaryConcatResult:
            raise TypeError("boundary concat memo contains another value sort")
        _validate_value(arena, key, found, published=True)
        if found != value:
            raise ValueError("boundary concat already has another canonical result")
        arena.ledger.bump("tile_boundary_concat_cache_late_duplicates")
        return found, False
    publish_indexed_result(arena, key, value)
    arena.ledger.bump("tile_boundary_concat_cache_publications")
    return value, True


def _validate_application(
    arena: CompletedResultArena,
    dependencies: TileDependencyLeases | None,
    application: int | None,
) -> None:
    if (dependencies is None) != (application is None):
        raise ValueError("concat dependency owner and application must be paired")
    if dependencies is None or application is None:
        return
    from number_compiler.hashlife.execution.tile_application_authority import (
        validate_application_dependencies,
    )
    from number_compiler.resources.tile_dependency_leases import TileDependencyLeases

    if type(dependencies) is not TileDependencyLeases:
        raise TypeError("concat dependency pin requires the scheduler lease store")
    if dependencies.ledger is not arena.ledger or dependencies.tiles is not arena.tiles:
        raise ValueError("concat dependency pin belongs to another index")
    if type(application) is not int or application < 0:
        raise ValueError("concat dependency pin has an invalid application identity")
    live = validate_application_dependencies(
        dependencies.applications,
        arena.ledger,
        arena.tiles,
        application,
    )
    arena.ledger.bump("tile_boundary_concat_application_validation_visits")
    if live.scheduler.results is not arena:
        raise ValueError("concat dependency pin requires one live application")


def _adjacent_same_backing(key: BoundaryConcatKey) -> bool:
    first, second = key.first, key.second
    return (
        first.tile == second.tile
        and first.orientation == second.orientation
        and (
            (
                not first.orientation
                and first.source_offset + first.relative_extent == second.source_offset
            )
            or (
                first.orientation == 1
                and second.source_offset + second.relative_extent == first.source_offset
            )
        )
    )


def concat_cached_boundary_views(
    arena: CompletedResultArena,
    alphabet: TileAlphabetID,
    first: BoundaryTileView,
    second: BoundaryTileView,
    *,
    dependencies: TileDependencyLeases | None = None,
    application: int | None = None,
) -> tuple[BoundaryTileView, TileLease]:
    """Return one leased exact concat, shared across actions and observations."""
    _validate_application(arena, dependencies, application)
    key = _key(arena, alphabet, first, second)
    if _adjacent_same_backing(key):
        merged, adjacent_lease = concat_boundary_views(
            arena.tiles,
            alphabet,
            key.first,
            key.second,
        )
        if merged is None or adjacent_lease is None:
            raise AssertionError("adjacent boundary concatenation lost its view")
        try:
            if dependencies is not None and application is not None:
                dependencies.acquire(application, (merged.tile,))
        except BaseException:
            adjacent_lease.close()
            raise
        return merged, adjacent_lease
    found = _lookup_canonical(arena, key)
    if found is not None:
        hit_lease = arena.tiles.retain(found.view.tile)
        try:
            if dependencies is not None and application is not None:
                dependencies.acquire(
                    application,
                    (key.first.tile, key.second.tile, found.view.tile),
                )
        except BaseException:
            hit_lease.close()
            raise
        return _view(found.view), hit_lease
    arena.ledger.bump("tile_boundary_concat_cache_evaluations")
    try:
        merged, miss_lease = concat_boundary_views(
            arena.tiles,
            alphabet,
            key.first,
            key.second,
        )
    except BaseException:
        arena.ledger.bump("tile_boundary_concat_cache_failures")
        raise
    if merged is None or miss_lease is None:
        raise AssertionError("boundary concatenation produced no exact content")
    raw_lease: TileLease | None = miss_lease
    result_lease: TileLease | None = None
    batch: DependencyLeaseBatch | None = None
    try:
        if not merged.orientation and not merged.source_offset:
            normalized, result_lease = _view(merged), miss_lease
            raw_lease = None
        else:
            normalized, result_lease = normalize_boundary_view(arena.tiles, merged)
        value = _sealed(arena, key, normalized)
        if dependencies is not None and application is not None:
            batch = dependencies.acquire(
                application,
                (key.first.tile, key.second.tile, value.view.tile),
            )
        published, _ = _publish(arena, key, value)
        if published.view.tile != result_lease.tile:
            result_lease.close()
            result_lease = arena.tiles.retain(published.view.tile)
        return _view(published.view), result_lease
    except BaseException:
        if batch is not None and dependencies is not None:
            dependencies.rollback(batch)
        if result_lease is not None:
            result_lease.close()
        arena.ledger.bump("tile_boundary_concat_cache_failures")
        raise
    finally:
        if raw_lease is not None:
            raw_lease.close()


__all__ = [
    "concat_cached_boundary_views",
    "lookup_boundary_concat",
]
