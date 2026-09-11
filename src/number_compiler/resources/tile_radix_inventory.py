"""Independent ownership checks for canonical tile radix projections."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tiles import TileLease
from number_compiler.projection.tile_radix import (
    MAX_TILE_RADIX,
    TileRadixObservation,
    TileRadixProjection,
    _valid_division_effect,
)


def _valid_lease(lease: object, projection: TileRadixProjection) -> bool:
    if type(lease) is not TileLease or lease._arena is not projection.scheduler.tiles:
        return False
    if type(lease._closed) is not bool or lease._closed is not projection._closed:
        return False
    if projection._closed:
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
            valid = (
                type(root.projection) is LazyProjection
                and root.projection.scheduler is root.scheduler
                and root.scheduler in schedulers
                and root.scheduler.ledger is ledger
                and type(root.adapter) is PrimitiveTileKernelAdapter
                and root.scheduler.adapter is root.adapter
                and 2 <= root.radix <= MAX_TILE_RADIX
                and containers.get(root._owner) is root._apps
                and type(root._closed) is bool
                and (not root._closed or not root._apps)
            )
            try:
                effect = root.adapter.kernels.kernel(
                    root.adapter._action(root.division).kernel,
                ).effect
                division_record = root.adapter._action(root.division)
                valid &= _valid_division_effect(effect, root.radix)
                valid &= (
                    division_record.cocycle == TemporalCocycle()
                    and division_record.spatial_events_add is False
                )
                source = None if root._closed else root.projection._open().source
                valid &= all(
                    type(index) is int
                    and index >= 0
                    and type(application) is TileApplication
                    and application in applications
                    and application.scheduler is root.scheduler
                    and application.source == source
                    and application._closed is False
                    for index, application in root._apps.items()
                )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(root), id(root._apps)))
            else:
                invalid.add((root._owner, id(root)))
        if type(root) is TileRadixProjection:
            valid = (
                root.ledger is ledger
                and root.scheduler in schedulers
                and type(root.adapter) is PrimitiveTileKernelAdapter
                and root.scheduler.adapter is root.adapter
                and 2 <= root.radix <= MAX_TILE_RADIX
                and containers.get(root._stage_owner) is root._stages
                and type(root._closed) is bool
                and _valid_lease(root._source, root)
            )
            try:
                primitive = root.adapter._action(root.action)
                effect = root.adapter.kernels.kernel(primitive.kernel).effect
                valid &= _valid_division_effect(effect, root.radix)
                valid &= (
                    primitive.cocycle == TemporalCocycle()
                    and primitive.spatial_events_add is False
                )
                expected_source = None if root._closed else root._source.tile
                valid &= not root._closed or not root._stages
                for exponent, stage in root._stages.items():
                    record = root.adapter._action(stage.action)
                    direct = (
                        stage.source == expected_source
                        and record.repetitions == exponent
                    )
                    valid &= (
                        type(exponent) is int
                        and exponent >= 1
                        and type(stage) is TileApplication
                        and stage.scheduler is root.scheduler
                        and stage._root is not None
                        and stage._closed is False
                        and record.kernel == primitive.kernel
                        and direct
                    )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(root), id(root._stages)))
            else:
                invalid.add((root._stage_owner, id(root)))
    return approved, invalid


__all__ = ["audit_tile_radix_runtime"]
