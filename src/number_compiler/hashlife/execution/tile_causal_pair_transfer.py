"""Consume a certified primitive-pair boundary through its finite interface.

This is the finite-transfer case of the causal recurrence.  The consumer's
directed exit is available from its existing parametric interface, so producing
the producer's exact boundary content would be unnecessary work.  Higher
temporal edges continue through canonical causal-output tiles.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.reverse_morphism_transfer import (
    ReverseMorphismTransferArena,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalPrefix,
    primitive_advance,
)
from number_compiler.hashlife.execution.tile_fused_kernel import fused_interface
from number_compiler.hashlife.tiles.interface_publication import (
    lookup_execution_fused_interface,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import FusedInterfaceKey

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def finite_pair_transfer(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    side: int,
    prefix: CausalPrefix,
    opposite: object,
    consumer: object,
) -> int | None:
    """Return a bounded consumer exit, or decline a nonprimitive edge.

    Spatial pieces are maximal dyadic input views, never emitted symbols or
    temporal stages. Both producer endpoints are transported before observing
    the consumer; its finite input remains a parameter of the cached function.
    """
    pair = engine.adapter.fused_primitive_pair(action)
    if pair is None:
        return None
    if type(side) is not int or side not in (0, 1):
        raise ValueError("causal transfer requires a directed side")
    if (
        type(prefix) is not CausalPrefix
        or prefix.action != action
        or prefix.side != side
    ):
        raise ValueError("causal transfer prefix belongs to another temporal edge")
    if type(opposite) is not int or type(consumer) is not int:
        raise TypeError("primitive-pair transfer requires finite endpoint states")
    if prefix.view is None:
        return consumer
    before, after = pair
    adapter, tiles = engine.adapter, engine.tiles
    chunks = engine._covered_chunks(prefix.view)
    left, right = prefix.producer_seed, opposite
    if side:
        chunks = tuple(engine._keep(tiles.mirror(tile)) for tile in reversed(chunks))
        left, right = right, left

    morphism = None
    laws = tuple(adapter.primitive_law(child) for child in pair)
    if all(type(law.effect) is BaseBlockEffect and law.base == 10 for law in laws):
        if adapter._reverse_morphism_transfer is None:
            adapter._reverse_morphism_transfer = ReverseMorphismTransferArena(
                tiles, adapter.bits, laws[0]
            )
        morphism = adapter._reverse_morphism_transfer
        if len(chunks) == 1:
            # Exterior producer states already bind this whole interval. Its
            # two exits are not needed to discover a nonexistent midpoint.
            result = morphism.consume(chunks[0], (left, right), side, consumer)
            engine.ledger.bump("tile_causal_finite_transfer_parent_observations")
            engine.ledger.bump("tile_causal_finite_pair_transfers")
            return result

    anchors = [left]
    # Only interior endpoints feed a chunk binding. The far exterior exits
    # would never be consumed by either the morphism or the fallback.
    for tile in chunks[:-1]:
        node = tiles.resolve(tile)
        anchors.append(
            primitive_advance(
                adapter,
                before,
                0,
                anchors[-1],
                BoundaryTileView(tile, 0, node.width),
            )
        )
    arguments = [right]
    for tile in reversed(chunks[1:]):
        node = tiles.resolve(tile)
        arguments.append(
            primitive_advance(
                adapter,
                before,
                1,
                arguments[-1],
                BoundaryTileView(tile, 0, node.width, 1),
            )
        )
    arguments.reverse()

    if morphism is None:
        wiring, producer_wiring = adapter.wiring(after), adapter.wiring(before)
        initial = adapter.initial_ports(after)
    order = range(len(chunks) - 1, -1, -1) if side else range(len(chunks))
    state = consumer
    for index in order:
        if morphism is not None:
            state = morphism.consume(
                chunks[index],
                (anchors[index], arguments[index]),
                side,
                state,
            )
            engine.ledger.bump("tile_causal_finite_transfer_parent_observations")
            continue
        key = FusedInterfaceKey(
            action,
            chunks[index],
            (anchors[index], arguments[index]),
            wiring,
            producer_wiring,
            before=before,
            after=after,
        )
        interface = lookup_execution_fused_interface(
            engine.scheduler.results,
            key,
        )
        if interface is None:
            interface = fused_interface(
                adapter,
                action,
                chunks[index],
                (anchors[index], arguments[index]),
                wiring,
                producer_wiring=producer_wiring,
            )
        ports = (initial[0], state) if side else (state, initial[1])
        state = adapter._observe(
            interface,
            "boundary_right" if side else "boundary_left",
            ports,
        )
        engine.ledger.bump("tile_causal_finite_transfer_parent_observations")
    engine.ledger.bump("tile_causal_finite_pair_transfers")
    return state


__all__ = ["finite_pair_transfer"]
