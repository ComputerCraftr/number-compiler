"""Demanded primitive-pair diamonds over canonical tiles and finite ports."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, Any, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    before_context,
    bind_context,
)
from number_compiler.hashlife.tiles.tile_ports import BoundPorts, FusedBoundaryContract
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def supports_fused_pair(scheduler: TileScheduler, action: FieldCellActionID) -> bool:
    hook = getattr(scheduler.adapter, "fused_primitive_pair", None)
    if hook is None:
        return False
    pair = cast(
        Callable[
            [FieldCellActionID], tuple[FieldCellActionID, FieldCellActionID] | None
        ],
        hook,
    )(action)
    return pair is not None


def demanded_fused_point(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    coordinate: int,
) -> int | None:
    if supports_fused_pair(scheduler, key.action):
        scheduler.ledger.bump("powered_absorption_requests")
        scheduler.ledger.bump("powered_absorption_evaluations")
        result = observe_fused_point(scheduler, key, coordinate)
        _absorption_success(scheduler, key.action)
        return result
    if getattr(scheduler.adapter, "fused_demand_only", False) is True:
        raise UnsupportedInterfaceError(
            "temporal demand has no bounded fused interface"
        )
    return None


def demanded_fused_width(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    limit: int,
) -> int | None:
    if supports_fused_pair(scheduler, key.action):
        scheduler.ledger.bump("powered_absorption_requests")
        scheduler.ledger.bump("powered_absorption_evaluations")
        result = observe_fused_width(scheduler, key, limit)
        _absorption_success(scheduler, key.action)
        return result
    if getattr(scheduler.adapter, "fused_demand_only", False) is True:
        raise UnsupportedInterfaceError(
            "temporal demand has no bounded fused interface"
        )
    return None


def _absorption_success(
    scheduler: TileScheduler,
    action: FieldCellActionID,
) -> None:
    scheduler.ledger.bump("powered_absorption_successes")
    span = scheduler.adapter.action_cocycle(action).physical_ticks
    previous = scheduler.ledger.counters.get("powered_absorption_max_span", 0)
    if span > previous:
        scheduler.ledger.bump("powered_absorption_max_span", span - previous)


def _initial_producer(
    scheduler: TileScheduler,
    key: PoweredResultKey,
) -> ChildContext:
    pair = cast(
        Callable[
            [FieldCellActionID], tuple[FieldCellActionID, FieldCellActionID] | None
        ],
        getattr(scheduler.adapter, "fused_primitive_pair"),
    )(key.action)
    if pair is None:
        raise UnsupportedInterfaceError(
            "demanded temporal output requires a bounded fused primitive pair"
        )
    context = before_context(scheduler, key, pair[0])
    if type(context) is not ChildContext:
        raise TypeError("fused producer returned another boundary context")
    return context


def _contexts(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    tile: TileID,
    contract: FusedBoundaryContract,
    side: int,
) -> FusedBoundaryContract:
    producer, consumer = contract.producer, contract.consumer
    hook = cast(Any, getattr(scheduler.adapter, "fused_child_contexts"))
    result = hook(
        key.action,
        tile,
        producer.ports,
        consumer.ports,
        consumer.wiring,
        side,
        producer_wiring=producer.wiring,
    )
    if (
        type(result) is not tuple
        or len(result) != 2
        or any(type(item) is not ChildContext for item in result)
    ):
        raise TypeError("fused sibling transfer returned another context")
    scheduler.ledger.bump("tile_scheduler_sibling_transfer_requests")
    scheduler.ledger.bump("tile_scheduler_sibling_transfer_evaluations")
    return FusedBoundaryContract(
        *(BoundPorts(value.ports, value.wiring, value.boundaries) for value in result)
    )


def _active(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    tile: TileID,
    contract: FusedBoundaryContract,
) -> bool:
    producer, consumer = contract.producer, contract.consumer
    # Causal interface preparation publishes the complete bound observation
    # for each demanded subtree.  Consume that result before asking the
    # primitive-pair fuser to reconstruct either sibling interface.
    from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
        causal_interface_key,
        lookup_causal_interface,
    )

    request = PoweredResultKey(
        key.action,
        tile,
        consumer.ports,
        consumer.wiring,
        consumer.boundaries,
        contract,
    )
    prepared = lookup_causal_interface(
        scheduler.results,
        causal_interface_key(key if tile == key.input else request),
    )
    if prepared is not None:
        return prepared.active
    hook = cast(Any, getattr(scheduler.adapter, "fused_output_active"))
    result = hook(
        key.action,
        tile,
        producer.ports,
        consumer.ports,
        consumer.wiring,
        producer_wiring=producer.wiring,
    )
    if type(result) is not bool:
        raise TypeError("fused activity returned another result sort")
    return result


def _initial_contract(
    scheduler: TileScheduler,
    key: PoweredResultKey,
) -> FusedBoundaryContract:
    producer = _initial_producer(scheduler, key)
    pair = scheduler.adapter.action_children(key.action)
    if pair is None:
        raise ValueError("fused contexts require a temporal edge")
    return FusedBoundaryContract(
        bind_context(
            scheduler,
            pair[0],
            BoundPorts(producer.ports, producer.wiring, producer.boundaries),
        ),
        bind_context(
            scheduler, pair[1], BoundPorts(key.ports, key.wiring, key.boundaries)
        ),
    )


def observe_fused_point(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    coordinate: int,
) -> int:
    """Observe B(A(X))[coordinate] without constructing A(X) or its sibling."""
    contract = _initial_contract(scheduler, key)
    tile = key.input
    scheduler.ledger.bump("tile_fused_observation_requests")
    while True:
        scheduler.ledger.bump("tile_fused_observation_descents")
        scheduler.ledger.bump("tile_fused_frames")
        node = scheduler.tiles.resolve(tile)
        if not node.level:
            hook = cast(Any, getattr(scheduler.adapter, "fused_leaf_result"))
            result = hook(
                key.action,
                tile,
                contract.producer.ports,
                contract.consumer.ports,
                contract.consumer.wiring,
                producer_wiring=contract.producer.wiring,
            )
            if type(result) is not PrimitiveTileResult:
                raise TypeError("fused leaf returned an incomplete result")
            scheduler.ledger.bump("tile_fused_leaf_evaluations")
            return result.symbol
        if node.left is None or node.right is None:
            raise ValueError("malformed canonical fused parent")
        half = 1 << (node.level - 1)
        side = int(coordinate >= half)
        contract = _contexts(scheduler, key, tile, contract, side)
        tile = node.right if side else node.left
        if side:
            coordinate -= half


def observe_fused_width(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    limit: int,
) -> int:
    """Find the rightmost active fused leaf using bounded subtree effects."""
    initial = _initial_contract(scheduler, key)
    pending: list[tuple[int, TileID, FusedBoundaryContract]] = [(0, key.input, initial)]
    scheduler.ledger.bump("tile_fused_observation_requests")
    while pending:
        peak = scheduler.ledger.counters.get("tile_fused_workspace_peak", 0)
        if len(pending) > peak:
            scheduler.ledger.bump("tile_fused_workspace_peak", len(pending) - peak)
        origin, tile, contract = pending.pop()
        scheduler.ledger.bump("tile_fused_frames")
        node = scheduler.tiles.resolve(tile)
        if origin >= limit:
            continue
        scheduler.ledger.bump("tile_fused_observation_descents")
        if origin + node.width <= limit and not _active(
            scheduler,
            key,
            tile,
            contract,
        ):
            continue
        if not node.level:
            return origin + 1
        if node.left is None or node.right is None:
            raise ValueError("malformed canonical fused parent")
        half = 1 << (node.level - 1)
        left = _contexts(scheduler, key, tile, contract, 0)
        right = _contexts(scheduler, key, tile, contract, 1)
        # LIFO: left is queued first so the rightmost branch is observed first.
        pending.append((origin, node.left, left))
        pending.append((origin + half, node.right, right))
    return 0


__all__ = ["demanded_fused_point", "demanded_fused_width"]
