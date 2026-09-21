"""Transient values and exact-boundary operations for causal tile tasks."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, Any

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
    boundary_dyadic_pieces,
    concat_boundary_views,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal_results import (
        CausalCompletedOutput,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.tiles.tile_ports import FusedBoundaryContract
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
    from number_compiler.hashlife.tiles.tile_results import (
        CompletedResultArena,
        ResultLease,
    )
    from number_compiler.resources.tile_dependency_leases import TileDependencyLeases


@dataclass(frozen=True, slots=True)
class CausalPrefix:
    action: FieldCellActionID
    side: int
    producer_seed: int
    consumer_seed: int
    view: BoundaryTileView | None = None
    consumer_view: BoundaryTileView | None = None
    explicit_edge: bool = False


@dataclass(slots=True)
class CausalFrame:
    op: str
    args: tuple[Any, ...]
    stage: int = 0
    saved: tuple[Any, ...] = ()
    memoized: bool = False


def edge_state(
    action: FieldCellActionID,
    side: int,
    producer_seed: int,
    consumer_seed: int,
    producer_view: BoundaryTileView | None,
    consumer_view: BoundaryTileView | None,
) -> CausalPrefix:
    return CausalPrefix(
        action,
        side,
        producer_seed,
        consumer_seed,
        producer_view,
        consumer_view,
        True,
    )


def bound_states(
    adapter: PrimitiveTileKernelAdapter,
    results: CompletedResultArena,
    action: FieldCellActionID,
    tile: TileID,
    contract: FusedBoundaryContract,
) -> tuple[CausalPrefix, CausalPrefix]:
    """Validate one explicit temporal edge and construct its two scan states."""
    contract.__post_init__()
    children = adapter.action_children(action)
    if children is None:
        raise ValueError("an explicit edge requires a composite action")
    before, after = children
    results.validate_shape(before, contract.producer.ports, contract.producer.wiring)
    results.validate_shape(after, contract.consumer.ports, contract.consumer.wiring)
    adapter.validate_input(action, tile)
    for child, bound in ((before, contract.producer), (after, contract.consumer)):
        if bound.boundaries.tile_ids():
            adapter.validate_boundaries(child, bound.boundaries, bound.wiring)
    producer, consumer = contract.producer, contract.consumer
    return (
        edge_state(
            action,
            0,
            producer.ports[0],
            consumer.ports[0],
            producer.boundaries.left,
            consumer.boundaries.left,
        ),
        edge_state(
            action,
            1,
            producer.ports[1],
            consumer.ports[1],
            producer.boundaries.right,
            consumer.boundaries.right,
        ),
    )


def primitive_advance(
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    side: int,
    state: int,
    view: BoundaryTileView,
    *,
    action_admission: object | None = None,
) -> int:
    """Apply a primitive directed transfer to one exact logical view."""
    from number_compiler.hashlife.tiles.tile_ports import BoundPorts

    if type(view) is not BoundaryTileView:
        raise TypeError("primitive advance requires a canonical boundary view")
    view.__post_init__()
    if type(side) is not int or side not in (0, 1):
        raise ValueError("primitive advance requires an exact directed side")
    if (
        view.orientation == side
        and not view.source_offset
        and view.relative_extent == adapter.tiles.resolve(view.tile).width
    ):
        # The operand already is the requested canonical parent.  The directed
        # memo validates action, alphabet, liveness and the incoming side; retain
        # the two-port admissibility check without entering another region walk.
        from number_compiler.hashlife.execution.tile_directed_transfer import (
            canonical_directed_transfer,
        )

        result = canonical_directed_transfer(
            adapter,
            action,
            view.tile,
            side,
            state,
            _action_admission=action_admission,
        )
        adapter.ledger.bump("tile_causal_direct_parent_transfers")
        return result
    scan_view = BoundaryTileView(
        view.tile,
        view.relative_origin,
        view.relative_extent,
        view.orientation ^ side,
        view.source_offset,
    )
    if action_admission is None:
        wiring = adapter.wiring(action)
        initial = adapter.initial_ports(action)
    else:
        # The token is the authority for the current causal run. Recover its
        # workspace only after checking its exact lease sort; the admission
        # helpers then authenticate the action metadata and reject foreign or
        # stale tokens before exposing wiring or initial ports.
        from number_compiler.hashlife.execution.tile_causal_admission import (
            admitted_kernel,
            admitted_wiring,
        )
        from number_compiler.resources.causal_workspace import (
            CausalActionAdmission,
        )

        if type(action_admission) is not CausalActionAdmission:
            raise TypeError("primitive advance requires a causal admission lease")
        tasks = action_admission._workspace
        wiring = admitted_wiring(adapter, tasks, action_admission, action)
        law = admitted_kernel(adapter, tasks, action_admission, action)
        initial = (
            law.initial(BoundarySide.LEFT),
            law.initial(BoundarySide.RIGHT),
        )
    ports = (state, initial[1]) if side == 0 else (initial[0], state)
    return adapter.transfer_view(action, scan_view, BoundPorts(ports, wiring), side)


def covered_chunks(
    tiles: TileArena,
    leases: list[TileLease],
    view: BoundaryTileView,
) -> tuple[TileID, ...]:
    """Return exact logical pieces in scan order, retaining mirrored results."""
    output: list[TileID] = []
    for piece in boundary_dyadic_pieces(tiles, view):
        if piece.orientation:
            lease = tiles.mirror(piece.tile)
            leases.append(lease)
            output.append(lease.tile)
        else:
            output.append(piece.tile)
    return tuple(output)


def scan_view(
    tiles: TileArena,
    leases: list[TileLease],
    view: BoundaryTileView,
    *,
    results: CompletedResultArena | None = None,
    dependencies: TileDependencyLeases | None = None,
    application: int | None = None,
) -> BoundaryTileView:
    """Normalize a clipped oriented view into exact scan-oriented content."""
    if not view.orientation:
        return BoundaryTileView(
            view.tile,
            0,
            view.relative_extent,
            0,
            view.source_offset,
        )
    source = tiles.resolve(view.tile)
    if not view.source_offset and view.relative_extent == source.width:
        # A whole oriented macrocell already has one canonical mirror in the
        # TileArena.  Decomposing it and concatenating the mirrored children
        # repeats the same spatial tree at every temporal layer.
        mirror_lease = tiles.mirror(view.tile)
        leases.append(mirror_lease)
        tiles.ledger.bump("tile_boundary_scan_whole_mirror_hits")
        return BoundaryTileView(mirror_lease.tile, 0, source.width)
    if results is not None:
        from number_compiler.hashlife.tiles.tile_region_memo import (
            normalize_cached_region,
        )

        normalized, region_lease = normalize_cached_region(
            results,
            BoundaryTileView(
                view.tile, 0, view.relative_extent, view.orientation, view.source_offset
            ),
            dependencies=dependencies,
            application=application,
        )
        leases.append(region_lease)
        tiles.ledger.bump("tile_boundary_scan_cached_region_requests")
        return normalized
    merged = None
    for tile in covered_chunks(tiles, leases, view):
        node = tiles.resolve(tile)
        merged, lease = concat_boundary_views(
            tiles,
            node.alphabet,
            merged,
            BoundaryTileView(tile, 0, node.width),
        )
        if lease is not None:
            leases.append(lease)
    if merged is None:
        raise ValueError("causal prefix cannot append an empty view")
    return BoundaryTileView(merged.tile, 0, view.relative_extent)


def append_prefix(
    adapter: PrimitiveTileKernelAdapter,
    tiles: TileArena,
    leases: list[TileLease],
    state: CausalPrefix,
    view: BoundaryTileView,
    *,
    results: CompletedResultArena | None = None,
    dependencies: TileDependencyLeases | None = None,
    application: int | None = None,
) -> CausalPrefix:
    """Append one exact causal operand without retaining an output program."""
    del adapter
    normalized = scan_view(
        tiles,
        leases,
        view,
        results=results,
        dependencies=dependencies,
        application=application,
    )
    if state.view is None:
        return CausalPrefix(
            state.action,
            state.side,
            state.producer_seed,
            state.consumer_seed,
            normalized,
            state.consumer_view,
            state.explicit_edge,
        )
    node = tiles.resolve(normalized.tile)
    if results is None:
        merged, lease = concat_boundary_views(
            tiles,
            node.alphabet,
            state.view,
            normalized,
        )
    else:
        from number_compiler.hashlife.tiles.tile_boundary_concat_memo import (
            concat_cached_boundary_views,
        )

        merged, lease = concat_cached_boundary_views(
            results,
            node.alphabet,
            state.view,
            normalized,
            dependencies=dependencies,
            application=application,
        )
    if lease is not None:
        leases.append(lease)
    return CausalPrefix(
        state.action,
        state.side,
        state.producer_seed,
        state.consumer_seed,
        merged,
        state.consumer_view,
        state.explicit_edge,
    )


def result_payload(tiles: TileArena, result: ResultLease) -> CausalCompletedOutput:
    """Detach immutable completed semantics from its owning result lease."""
    from number_compiler.hashlife.execution.tile_causal_results import (
        cached_causal_output,
    )

    return cached_causal_output(result, tiles)


def temporal_payload(
    adapter: PrimitiveTileKernelAdapter,
    before: FieldCellActionID,
    after: FieldCellActionID,
    first: CausalCompletedOutput,
    second: CausalCompletedOutput,
    explicit_edge: bool,
) -> CausalCompletedOutput:
    """Compose one transient temporal edge without retaining its derivation."""
    from number_compiler.hashlife.tiles.tile_ports import (
        BoundPorts,
        FusedBoundaryContract,
    )

    fusion = None
    if explicit_edge:
        fusion = FusedBoundaryContract(
            BoundPorts(
                first.semantics.outgoing_ports,
                adapter.wiring(before),
                first.semantics.outgoing_boundaries,
            ),
            BoundPorts(
                second.semantics.outgoing_ports,
                adapter.wiring(after),
                second.semantics.outgoing_boundaries,
            ),
        )
    from number_compiler.hashlife.execution.tile_physical_support import (
        temporal_physical_support,
    )

    return replace(
        second,
        semantics=replace(
            second.semantics,
            physical_ticks=(
                first.semantics.physical_ticks + second.semantics.physical_ticks
            ),
            event_weight=(first.semantics.event_weight + second.semantics.event_weight),
            frame_shift=first.semantics.frame_shift + second.semantics.frame_shift,
            fusion=fusion,
            physical_support=temporal_physical_support(
                first.semantics.physical_support,
                second.semantics.physical_support,
                before_ticks=first.semantics.physical_ticks,
                after_ticks=second.semantics.physical_ticks,
            ),
        ),
    )


def producer_parent(
    tiles: TileArena,
    leases: list[TileLease],
    left: CausalCompletedOutput,
    right: CausalCompletedOutput,
) -> TileID | None:
    """Join the explicit producer outputs carried by two fused children."""
    left_edge, right_edge = left.semantics.fusion, right.semantics.fusion
    if left_edge is None and right_edge is None:
        return None
    if left_edge is None or right_edge is None:
        raise ValueError("causal children disagree on producer output presence")
    left_view = left_edge.producer.boundaries.left
    right_view = right_edge.producer.boundaries.left
    if left_view is None or right_view is None:
        raise ValueError("fused child omitted its exact producer output")
    lease = tiles.join(left_view.tile, right_view.tile)
    leases.append(lease)
    return lease.tile


def composite_result_key(
    adapter: PrimitiveTileKernelAdapter,
    results: CompletedResultArena,
    action: FieldCellActionID,
    tile: TileID,
    left: object,
    right: object,
    *,
    action_admission: object | None = None,
) -> PoweredResultKey | None:
    """Build a key only when the exact edge context is represented."""
    from number_compiler.hashlife.execution.tile_causal_results import (
        CompositeCausalPrefixes,
        causal_result_key,
    )
    from number_compiler.hashlife.tiles.tile_ports import (
        BoundPorts,
        FusedBoundaryContract,
        ResultWiring,
    )
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

    if not isinstance(left, CausalPrefix) or not isinstance(right, CausalPrefix):
        return None
    if (left.action, left.side) != (action, 0) or (right.action, right.side) != (
        action,
        1,
    ):
        raise ValueError("composite causal prefixes have another action or direction")
    if action_admission is None:
        children = adapter.action_children(action)
        action_wiring = adapter.wiring(action)
    else:
        from number_compiler.resources.causal_workspace import (
            admitted_action_metadata,
        )

        signature, _kernel, record = admitted_action_metadata(
            action_admission, adapter, action
        )
        children = record.children
        action_wiring = ResultWiring(signature)
    if children is None:
        return None
    before, _after = children
    if action_admission is None:
        initial = adapter.initial_ports(before)
        before_wiring = adapter.wiring(before)
        after_wiring = adapter.wiring(_after)
    else:
        before_signature, before_kernel, _before_record = admitted_action_metadata(
            action_admission, adapter, before
        )
        after_signature, _after_kernel, _after_record = admitted_action_metadata(
            action_admission, adapter, _after
        )
        kernel = adapter.kernels.kernel(before_kernel)
        initial = (
            kernel.initial(BoundarySide.LEFT),
            kernel.initial(BoundarySide.RIGHT),
        )
        before_wiring = ResultWiring(before_signature)
        after_wiring = ResultWiring(after_signature)
    if left.explicit_edge or right.explicit_edge:
        producer = BoundPorts(
            (left.producer_seed, right.producer_seed),
            before_wiring,
            BoundaryTileOperands(left.view, right.view),
        )
        consumer_boundaries = BoundaryTileOperands(
            left.consumer_view,
            right.consumer_view,
        )
        consumer = BoundPorts(
            (left.consumer_seed, right.consumer_seed),
            after_wiring,
            consumer_boundaries,
        )
        key = PoweredResultKey(
            action,
            tile,
            consumer.ports,
            action_wiring,
            consumer_boundaries,
            FusedBoundaryContract(producer, consumer),
        )
        results._validate_key(key, action_admission=action_admission)
        return key
    if (
        left.consumer_view is not None
        or right.consumer_view is not None
        or (left.producer_seed != initial[0] or right.producer_seed != initial[1])
    ):
        return None
    state = CompositeCausalPrefixes(
        (left.consumer_seed, right.consumer_seed),
        BoundaryTileOperands(left.view, right.view),
    )
    return causal_result_key(
        results,
        action,
        tile,
        state,
        action_wiring,
        action_admission=action_admission,
    )


__all__ = [
    "CausalFrame",
    "CausalPrefix",
    "append_prefix",
    "bound_states",
    "composite_result_key",
    "covered_chunks",
    "edge_state",
    "primitive_advance",
    "producer_parent",
    "result_payload",
    "temporal_payload",
]
