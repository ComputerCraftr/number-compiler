"""Persistent non-owning aliases for canonical clipped tile regions."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
    normalize_boundary_view,
)
from number_compiler.hashlife.tiles.tile_causal_interface_memo import _view_snapshot
from number_compiler.hashlife.tiles.tile_result_records import (
    NormalizedRegionKey,
    NormalizedRegionResult,
)
from number_compiler.hashlife.tiles.tile_result_validation import (
    validate_boundary_operands,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileID, TileLease
from number_compiler.resources.result_cache_kinds import (
    record_unattributed_post_eviction_miss,
)

if TYPE_CHECKING:
    from number_compiler.resources.tile_dependency_leases import (
        DependencyLeaseBatch,
        TileDependencyLeases,
    )


def _snapshot(
    key: NormalizedRegionKey,
    value: NormalizedRegionResult,
) -> tuple[object, ...]:
    return (_view_snapshot(key.view), _view_snapshot(value.view))


def _detached_view(view: BoundaryTileView) -> BoundaryTileView:
    """Copy every caller-owned scalar and scoped handle before retention."""
    tile = TileID(view.tile.owner, view.tile.kind, view.tile.local_id)
    return BoundaryTileView(
        tile,
        view.relative_origin,
        view.relative_extent,
        view.orientation,
        view.source_offset,
    )


def _detached_key(
    arena: CompletedResultArena,
    view: BoundaryTileView,
) -> NormalizedRegionKey:
    candidate = NormalizedRegionKey(view)
    _validate_key(arena, candidate)
    return NormalizedRegionKey(_detached_view(view))


def _validate_key(arena: CompletedResultArena, key: NormalizedRegionKey) -> None:
    if type(arena) is not CompletedResultArena:
        raise TypeError("region normalization requires the shared result arena")
    if type(key) is not NormalizedRegionKey:
        raise TypeError("region normalization has another key sort")
    if type(key.view) is not BoundaryTileView:
        raise TypeError("region normalization requires an exact clipped view")
    validate_boundary_operands(arena.tiles, BoundaryTileOperands(key.view))
    if key.view.relative_extent == 0:
        raise ValueError("region normalization requires a nonempty clipped view")


def _validate_value(
    arena: CompletedResultArena,
    key: NormalizedRegionKey,
    value: NormalizedRegionResult,
    *,
    published: bool,
) -> None:
    value.__post_init__()
    validate_boundary_operands(arena.tiles, BoundaryTileOperands(value.view))
    source = arena.tiles.resolve(key.view.tile)
    output = arena.tiles.resolve(value.view.tile)
    if source.alphabet != output.alphabet:
        raise ValueError("normalized region changed its tile alphabet")
    if (
        value.view.relative_origin != key.view.relative_origin
        or value.view.relative_extent != key.view.relative_extent
        or value.view.orientation != 0
        or value.view.source_offset != 0
        or output.width < value.view.relative_extent
    ):
        raise ValueError("normalized region changed its logical geometry")
    if published:
        if value._publication_owner is not arena._interface_publication_seal:
            raise ValueError("normalized region was not issued by this arena")
        if value._publication_snapshot != _snapshot(key, value):
            raise ValueError("normalized region publication metadata was modified")


def _sealed(
    arena: CompletedResultArena,
    key: NormalizedRegionKey,
    view: BoundaryTileView,
) -> NormalizedRegionResult:
    plain = NormalizedRegionResult(view)
    return NormalizedRegionResult(
        view,
        arena._interface_publication_seal,
        _snapshot(key, plain),
    )


def lookup_normalized_region(
    arena: CompletedResultArena,
    key: NormalizedRegionKey,
) -> NormalizedRegionResult | None:
    """Probe a validated raw clip before any spatial decomposition occurs."""
    _validate_key(arena, key)
    arena.ledger.bump("tile_region_normalization_requests")
    found = arena._memo.get(key)
    if found is None:
        arena.ledger.bump("tile_region_normalization_misses")
        record_unattributed_post_eviction_miss(arena.ledger, "region")
        return None
    if type(found) is not NormalizedRegionResult:
        raise TypeError("normalized region memo contains another value sort")
    _validate_value(arena, key, found, published=True)
    arena.ledger.bump("tile_region_normalization_early_hits")
    return found


def _publish(
    arena: CompletedResultArena,
    key: NormalizedRegionKey,
    value: NormalizedRegionResult,
) -> tuple[NormalizedRegionResult, bool]:
    _validate_key(arena, key)
    _validate_value(arena, key, value, published=True)
    found = arena._memo.get(key)
    arena.ledger.bump("tile_region_normalization_publication_requests")
    if found is not None:
        if type(found) is not NormalizedRegionResult:
            raise TypeError("normalized region memo contains another value sort")
        _validate_value(arena, key, found, published=True)
        if found != value:
            raise ValueError("clipped region already has another canonical result")
        arena.ledger.bump("tile_region_normalization_late_duplicates")
        return found, False
    referenced = arena._tiles_for(key, value)
    reverse_entries = arena._index_entries(referenced)
    reservations = (
        (arena._memo_owner, 1, 0),
        (arena._reverse_owner, reverse_entries, 0),
    )
    arena.ledger.reserve_many(reservations)
    reverse_snapshot = arena._reverse_snapshot(referenced, key)
    try:
        arena._memo[key] = value
        for tile in referenced:
            arena._add_membership(tile, key)
    except BaseException:
        arena._memo.pop(key, None)
        arena._restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            arena.ledger.release(owner, entries, nodes)
        raise
    arena.ledger.bump("tile_region_normalization_publications")
    return value, True


def normalize_cached_region(
    arena: CompletedResultArena,
    view: BoundaryTileView,
    *,
    dependencies: TileDependencyLeases | None = None,
    application: int | None = None,
) -> tuple[BoundaryTileView, TileLease]:
    """Return a leased canonical clip, preserving it across observations.

    The persistent memo is non-owning.  An application dependency root, when
    supplied, pins both the raw occurrence and its canonical result.  A failed
    publication rolls back every dependency binding created by this call.
    """
    if (dependencies is None) != (application is None):
        raise ValueError("region dependency owner and application must be paired")
    if dependencies is not None and application is not None:
        from number_compiler.hashlife.execution.tile_application_authority import (
            validate_application_dependencies,
        )
        from number_compiler.resources.tile_dependency_leases import (
            TileDependencyLeases,
        )

        if type(dependencies) is not TileDependencyLeases:
            raise TypeError("region dependency pin requires the scheduler lease store")
        if (
            dependencies.ledger is not arena.ledger
            or dependencies.tiles is not arena.tiles
        ):
            raise ValueError("region dependency pin belongs to another index")
        if type(application) is not int or application < 0:
            raise ValueError(
                "region dependency pin has an invalid application identity"
            )
        # The scheduler registry is the authenticated application index.  Count
        # the one exact lookup, including a stale-ID failure, without walking
        # every unrelated execution root on each cold or warm region request.
        arena.ledger.bump("tile_region_application_validation_visits")
        live = validate_application_dependencies(
            dependencies.applications,
            arena.ledger,
            arena.tiles,
            application,
        )
        if live.scheduler.results is not arena:
            raise ValueError("region dependency pin requires one live application")
    key = _detached_key(arena, view)
    view = key.view
    found = lookup_normalized_region(arena, key)
    if found is not None:
        lease = arena.tiles.retain(found.view.tile)
        try:
            if dependencies is not None and application is not None:
                dependencies.acquire(application, (view.tile, found.view.tile))
        except BaseException:
            lease.close()
            raise
        return _detached_view(found.view), lease

    normalized, lease = normalize_boundary_view(arena.tiles, view)
    value = _sealed(arena, key, normalized)
    batch: DependencyLeaseBatch | None = None
    try:
        if dependencies is not None and application is not None:
            batch = dependencies.acquire(application, (view.tile, normalized.tile))
        published, _ = _publish(arena, key, value)
        if published.view != normalized:
            lease.close()
            lease = arena.tiles.retain(published.view.tile)
        return _detached_view(published.view), lease
    except BaseException:
        if batch is not None and dependencies is not None:
            dependencies.rollback(batch)
        lease.close()
        raise


__all__ = [
    "NormalizedRegionKey",
    "NormalizedRegionResult",
    "lookup_normalized_region",
    "normalize_cached_region",
]
