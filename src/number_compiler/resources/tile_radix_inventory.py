"""Independent ownership checks for canonical tile radix projections."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.arithmetic.radix_division import (
    certified_binary_division_radix,
)
from number_compiler.hashlife.actions.tile_action_algebra import PrimitiveTileAction
from number_compiler.hashlife.execution.tile_application import TileApplication
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tiles import TileLease
from number_compiler.projection.tile_radix import (
    MAX_TILE_RADIX,
    TileRadixObservation,
    TileRadixProjection,
)


def _valid_binary_division(
    adapter: PrimitiveTileKernelAdapter,
    record: PrimitiveTileAction,
    radix: object,
) -> bool:
    effect = adapter.kernels.kernel(record.kernel).effect
    return (
        type(radix) is int
        and certified_binary_division_radix(effect) == radix
        and record.cocycle == TemporalCocycle()
        and record.spatial_events_add is False
    )


def _valid_lease(lease: object, projection: TileRadixProjection) -> bool:
    if type(lease) is not TileLease:
        return False
    lease_snapshot = lease.audit_snapshot()
    projection_snapshot = projection.audit_snapshot()
    if lease_snapshot.arena is not projection.scheduler.tiles:
        return False
    if (
        type(lease_snapshot.closed) is not bool
        or lease_snapshot.closed is not projection_snapshot.closed
    ):
        return False
    if projection_snapshot.closed:
        return True
    try:
        projection.scheduler.tiles.resolve(lease.tile)
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False
    return True


def audit_tile_radix_runtime(
    ledger: object,
    containers: Mapping[int, object],
    roots: tuple[object, ...],
    schedulers: tuple[TileScheduler, ...],
    applications: tuple[TileApplication, ...],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate radix consumers without interpreting their semantic results."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in roots:
        if type(root) is TileRadixObservation:
            snapshot = root.audit_snapshot()
            valid = (
                type(root.projection) is LazyProjection
                and root.projection.scheduler is root.scheduler
                and root.scheduler in schedulers
                and root.scheduler.ledger is ledger
                and type(root.adapter) is PrimitiveTileKernelAdapter
                and root.scheduler.adapter is root.adapter
                and 2 <= root.radix <= MAX_TILE_RADIX
                and (container := containers.get(snapshot.owner)) is not None
                and id(container) == snapshot.app_store_identity
                and type(snapshot.closed) is bool
                and (not snapshot.closed or not snapshot.apps)
            )
            try:
                division_record = root.adapter.action_record(root.division)
                valid &= _valid_binary_division(
                    root.adapter, division_record, root.radix
                )
                source = (
                    None
                    if snapshot.closed
                    else root.projection.validated_application().source
                )
                valid &= all(
                    type(index) is int
                    and index >= 0
                    and type(application) is TileApplication
                    and application in applications
                    and application.scheduler is root.scheduler
                    and application.source == source
                    and application.audit_snapshot().closed is False
                    for index, application in snapshot.apps.items()
                )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(root), snapshot.app_store_identity))
            else:
                invalid.add((snapshot.owner, id(root)))
        if type(root) is TileRadixProjection:
            projection_snapshot = root.audit_snapshot()
            valid = (
                root.ledger is ledger
                and root.scheduler in schedulers
                and type(root.adapter) is PrimitiveTileKernelAdapter
                and root.scheduler.adapter is root.adapter
                and 2 <= root.radix <= MAX_TILE_RADIX
                and (container := containers.get(projection_snapshot.stage_owner))
                is not None
                and id(container) == projection_snapshot.stage_store_identity
                and type(projection_snapshot.closed) is bool
                and _valid_lease(projection_snapshot.source, root)
            )
            try:
                primitive = root.adapter.action_record(root.action)
                valid &= _valid_binary_division(root.adapter, primitive, root.radix)
                expected_source = (
                    None
                    if projection_snapshot.closed
                    else projection_snapshot.source.tile
                )
                valid &= (
                    not projection_snapshot.closed or not projection_snapshot.stages
                )
                for exponent, stage in projection_snapshot.stages.items():
                    record = root.adapter.action_record(stage.action)
                    stage_snapshot = stage.audit_snapshot()
                    direct = (
                        stage.source == expected_source
                        and record.repetitions == exponent
                    )
                    valid &= (
                        type(exponent) is int
                        and exponent >= 1
                        and type(stage) is TileApplication
                        and stage.scheduler is root.scheduler
                        and stage_snapshot.root_lease is not None
                        and stage_snapshot.closed is False
                        and record.kernel == primitive.kernel
                        and direct
                    )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(root), projection_snapshot.stage_store_identity))
            else:
                invalid.add((projection_snapshot.stage_owner, id(root)))
    return approved, invalid


__all__ = ["audit_tile_radix_runtime"]
