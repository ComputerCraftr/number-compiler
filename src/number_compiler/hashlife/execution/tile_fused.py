"""Demanded primitive-pair diamonds over canonical tiles and finite ports."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, Protocol, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    before_context,
    bind_context,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


class FusedExecutionAdapter(Protocol):
    """Optional adapter surface required after a fused pair is accepted."""

    def fused_primitive_pair(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...

    def fused_child_contexts(
        self,
        action: FieldCellActionID,
        parent: TileID,
        producer_ports: tuple[int, ...],
        consumer_ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> tuple[ChildContext, ChildContext]: ...

    def fused_leaf_result(
        self,
        action: FieldCellActionID,
        source: TileID,
        producer_ports: tuple[int, ...],
        consumer_ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> PrimitiveTileResult: ...

    def fused_output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        producer_ports: tuple[int, ...],
        consumer_ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> bool: ...


def _fused_adapter(scheduler: TileScheduler) -> FusedExecutionAdapter:
    """Type the optional structural hooks at the adapter extension boundary.

    Each selected path still accesses its own hook normally; a pair probe alone
    does not validate other hooks or authorize substituting successor state.
    """
    return cast("FusedExecutionAdapter", scheduler.adapter)


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
        scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_REQUESTS)
        scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_EVALUATIONS)
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
        scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_REQUESTS)
        scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_EVALUATIONS)
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
    scheduler.ledger.bump(_execution_keys.POWERED_ABSORPTION_SUCCESSES)
    span = scheduler.adapter.action_cocycle(action).physical_ticks
    previous = scheduler.ledger.counters.get(
        _execution_keys.POWERED_ABSORPTION_MAX_SPAN, 0
    )
    if span > previous:
        scheduler.ledger.bump(
            _execution_keys.POWERED_ABSORPTION_MAX_SPAN, span - previous
        )


def _initial_producer(
    scheduler: TileScheduler,
    key: PoweredResultKey,
) -> ChildContext:
    pair = _fused_adapter(scheduler).fused_primitive_pair(key.action)
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
    result = _fused_adapter(scheduler).fused_child_contexts(
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
    scheduler.ledger.bump(_execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_REQUESTS)
    scheduler.ledger.bump(_execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_EVALUATIONS)
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
    result = _fused_adapter(scheduler).fused_output_active(
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
    scheduler.ledger.bump(_execution_keys.TILE_FUSED_OBSERVATION_REQUESTS)
    while True:
        scheduler.ledger.bump(_execution_keys.TILE_FUSED_OBSERVATION_DESCENTS)
        scheduler.ledger.bump(_execution_keys.TILE_FUSED_FRAMES)
        node = scheduler.tiles.resolve(tile)
        if not node.level:
            result = _fused_adapter(scheduler).fused_leaf_result(
                key.action,
                tile,
                contract.producer.ports,
                contract.consumer.ports,
                contract.consumer.wiring,
                producer_wiring=contract.producer.wiring,
            )
            if type(result) is not PrimitiveTileResult:
                raise TypeError("fused leaf returned an incomplete result")
            scheduler.ledger.bump(_execution_keys.TILE_FUSED_LEAF_EVALUATIONS)
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
    scheduler.ledger.bump(_execution_keys.TILE_FUSED_OBSERVATION_REQUESTS)
    while pending:
        peak = scheduler.ledger.counters.get(_shared_keys.TILE_FUSED_WORKSPACE_PEAK, 0)
        if len(pending) > peak:
            scheduler.ledger.bump(
                _shared_keys.TILE_FUSED_WORKSPACE_PEAK, len(pending) - peak
            )
        origin, tile, contract = pending.pop()
        scheduler.ledger.bump(_execution_keys.TILE_FUSED_FRAMES)
        node = scheduler.tiles.resolve(tile)
        if origin >= limit:
            continue
        scheduler.ledger.bump(_execution_keys.TILE_FUSED_OBSERVATION_DESCENTS)
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
