"""Admission of deep demanded output into the tile scheduler's causal tasks."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.tiles.tile_boundaries import EMPTY_BOUNDARY_TILES
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def causal_point(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    coordinate: int,
    *,
    application: int | None = None,
) -> int | None:
    """Execute a deep canonical-exterior request after its parent memo misses.

    Primitive and primitive-pair requests keep their existing finite transfer
    path. Unsupported edge assignments must not silently become initial ports.
    """
    if type(coordinate) is not int:
        raise TypeError("causal coordinate requires an exact integer")
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    children = adapter.action_children(key.action)
    if children is None or all(
        adapter.action_children(child) is None for child in children
    ):
        return None
    scheduler.results._validate_key(key)
    if not 0 <= coordinate < scheduler.tiles.resolve(key.input).width:
        raise IndexError(coordinate)
    if key.fusion is None and (
        key.ports != adapter.initial_ports(key.action)
        or key.boundaries != EMPTY_BOUNDARY_TILES
    ):
        raise UnsupportedInterfaceError(
            "deep causal output requires an executable explicit edge assignment"
        )
    scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_REQUESTS)
    scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_EVALUATIONS)
    engine = CausalTileEngine(scheduler)
    hooks = adapter.family_hooks
    root_shift = None if hooks is None else hooks.shifted_event(scheduler, key)
    if root_shift is not None:
        primitive, shift = root_shift
        mapped = coordinate + shift
        node = scheduler.tiles.resolve(key.input)
        result = (
            scheduler.tiles.alphabet(node.alphabet).blank
            if mapped >= node.width
            else engine.point(primitive, key.input, mapped, application=application)
        )
        scheduler.ledger.bump(_execution_keys.COLLATZ_INITIAL_ROOT_POINT_SKIPS)
        scheduler.ledger.bump(_shared_keys.COLLATZ_INITIAL_ROOT_SKIPPED_TICKS, shift)
    else:
        result = (
            engine.point(key.action, key.input, coordinate, application=application)
            if key.fusion is None
            else engine.point_bound(
                key.action,
                key.input,
                coordinate,
                key.fusion,
                application=application,
            )
        )
    _record_absorption(scheduler, key.action, adapter)
    return result


def causal_complete(
    scheduler: TileScheduler,
    key: PoweredResultKey,
) -> ResultLease | None:
    """Complete an explicitly requested output through causal macro tasks."""
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if (
        type(adapter) is not PrimitiveTileKernelAdapter
        or adapter.action_children(key.action) is None
    ):
        return None
    scheduler.results._validate_key(key)
    if key.fusion is None and key.ports != adapter.initial_ports(key.action):
        raise ValueError("complete causal powers require canonical exterior ports")
    if key.fusion is None and key.boundaries != EMPTY_BOUNDARY_TILES:
        raise UnsupportedInterfaceError(
            "explicit causal completion requires its bound edge executor"
        )
    scheduler.ledger.bump(_execution_keys.TILE_SCHEDULER_TEMPORAL_COMPLETE_REQUESTS)
    scheduler.ledger.bump(_execution_keys.TILE_CAUSAL_COMPLETE_REQUESTS)
    engine = CausalTileEngine(scheduler)
    output = (
        engine.output(key.action, key.input)
        if key.fusion is None
        else engine.output_bound(
            key.action,
            key.input,
            key.fusion,
        )
    )
    with output:
        result = scheduler.results.lookup(key)
        if result is None:
            raise AssertionError(
                "causal completion did not publish its completed parent"
            )
        return result


def causal_width_query(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    limit: int,
    *,
    application: int | None = None,
) -> int | None:
    """Observe a deep action's activity through the causal interface tasks."""
    if type(limit) is not int:
        raise TypeError("causal width limit requires an exact integer")
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
        reverse_sector_width_from_interface,
        supports_reverse_sector_width,
    )

    if key.fusion is None and supports_reverse_sector_width(adapter, key.action):
        from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
            causal_interface_key,
            lookup_causal_interface,
        )

        prepared = lookup_causal_interface(
            scheduler.results,
            causal_interface_key(key),
        )
        if prepared is not None:
            width = reverse_sector_width_from_interface(
                adapter,
                key.action,
                key.input,
                prepared,
                limit,
            )
            if width is not None:
                scheduler.ledger.bump(_execution_keys.TILE_CAUSAL_INTERFACE_PARENT_HITS)
                return width

    children = adapter.action_children(key.action)
    shallow = children is None or all(
        adapter.action_children(child) is None for child in children
    )
    if children is not None and shallow:
        # A primitive pair has a complete fused interface implementation.
        # Leave it to demanded_fused_width, just as causal_point does, before
        # constructing an oriented causal prefix for the sector shortcut.
        return None
    if shallow and (
        key.fusion is not None
        or key.ports != adapter.initial_ports(key.action)
        or key.boundaries != EMPTY_BOUNDARY_TILES
        or not supports_reverse_sector_width(adapter, key.action)
    ):
        return None
    scheduler.results._validate_key(key)
    if not 0 <= limit <= scheduler.tiles.resolve(key.input).width:
        raise ValueError("causal width limit lies outside the input tile")
    if key.fusion is None and (
        key.ports != adapter.initial_ports(key.action)
        or key.boundaries != EMPTY_BOUNDARY_TILES
    ):
        raise UnsupportedInterfaceError(
            "deep causal width requires an explicit edge assignment"
        )
    scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_REQUESTS)
    scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_EVALUATIONS)
    hooks = adapter.family_hooks
    root_shift = None if hooks is None else hooks.shifted_event(scheduler, key)
    if root_shift is not None:
        primitive, shift = root_shift
        node = scheduler.tiles.resolve(key.input)
        width = max(
            0,
            CausalTileEngine(scheduler).width(
                primitive,
                key.input,
                limit=min(node.width, limit + shift),
                application=application,
            )
            - shift,
        )
        scheduler.ledger.bump(_execution_keys.COLLATZ_INITIAL_ROOT_WIDTH_SKIPS)
        scheduler.ledger.bump(_shared_keys.COLLATZ_INITIAL_ROOT_SKIPPED_TICKS, shift)
    else:
        width = CausalTileEngine(scheduler).width(
            key.action,
            key.input,
            limit=limit,
            application=application,
            contract=key.fusion,
        )
    _record_absorption(scheduler, key.action, adapter)
    return width


__all__ = ["causal_complete", "causal_point", "causal_width_query"]


def _record_absorption(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    adapter: PrimitiveTileKernelAdapter,
) -> None:
    scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_SUCCESSES)
    span = adapter.action_cocycle(action).physical_ticks
    previous = scheduler.ledger.counters.get(
        _execution_keys.POWERED_ABSORPTION_MAX_SPAN, 0
    )
    if span > previous:
        scheduler.ledger.bump(
            _execution_keys.POWERED_ABSORPTION_MAX_SPAN, span - previous
        )
