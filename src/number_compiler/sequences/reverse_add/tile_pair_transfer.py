"""Consume a certified primitive-pair boundary through its finite interface.

This is the finite-transfer case of the causal recurrence.  The consumer's
directed exit is available from its existing parametric interface, so producing
the producer's exact boundary content would be unnecessary work.  Higher
temporal edges continue through canonical causal-output tiles.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalPrefix,
    primitive_advance,
)
from number_compiler.hashlife.execution.tile_execution_adapter import (
    FinitePairTransfer,
    FinitePairTransferFactory,
)
from number_compiler.hashlife.execution.tile_fused_kernel import fused_interface
from number_compiler.hashlife.tiles.interface_publication import (
    lookup_execution_fused_interface,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import FusedInterfaceKey
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.reverse_morphism_transfer import (
    ReverseMorphismTransferArena,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.resources.ledger import ResourceLedger


class ReverseAddFinitePairTransfer(FinitePairTransfer):
    """Reverse/add's exact finite pair consumer and decimal morphism cache."""

    def __init__(self, ledger: ResourceLedger) -> None:
        super().__init__(ledger)
        self._morphism: ReverseMorphismTransferArena | None = None
        ledger.register_execution_root(self)

    def clear_bindings(self) -> None:
        if self._morphism is not None:
            self._morphism.clear_bindings()

    @property
    def morphism_arena(self) -> ReverseMorphismTransferArena | None:
        """Expose the owned arena to family-local validation and diagnostics."""
        return self._morphism

    def transfer(
        self,
        engine: CausalTileEngine,
        action: FieldCellActionID,
        side: int,
        prefix: CausalPrefix,
        opposite: object,
        consumer: object,
    ) -> int | None:
        if engine.ledger is not self.ledger:
            raise ValueError("reverse pair transfer belongs to another ledger")
        return _finite_pair_transfer(
            self, engine, action, side, prefix, opposite, consumer
        )


class ReverseAddFinitePairTransferFactory(FinitePairTransferFactory):
    """Create the reverse strategy at each admitted tile runtime boundary."""

    def create(self, ledger: ResourceLedger) -> ReverseAddFinitePairTransfer:
        return ReverseAddFinitePairTransfer(ledger)


def _finite_pair_transfer(
    strategy: ReverseAddFinitePairTransfer,
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
    laws = tuple(engine._law(child) for child in pair)
    if all(type(law.effect) is BaseBlockEffect and law.base == 10 for law in laws):
        if strategy._morphism is None:
            strategy._morphism = ReverseMorphismTransferArena(
                tiles, adapter.bits, laws[0]
            )
        morphism = strategy._morphism
        if len(chunks) == 1:
            # Exterior producer states already bind this whole interval. Its
            # two exits are not needed to discover a nonexistent midpoint.
            result = morphism.consume(chunks[0], (left, right), side, consumer)
            engine.ledger.bump(
                _reverse_add_keys.TILE_CAUSAL_FINITE_TRANSFER_PARENT_OBSERVATIONS
            )
            engine.ledger.bump(_reverse_add_keys.TILE_CAUSAL_FINITE_PAIR_TRANSFERS)
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
                action_admission=engine._action_admission_token,
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
                action_admission=engine._action_admission_token,
            )
        )
    arguments.reverse()

    if morphism is None:
        wiring, producer_wiring = engine._wiring(after), engine._wiring(before)
        after_law = engine._law(after)
        initial = (
            after_law.initial(BoundarySide.LEFT),
            after_law.initial(BoundarySide.RIGHT),
        )
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
            engine.ledger.bump(
                _reverse_add_keys.TILE_CAUSAL_FINITE_TRANSFER_PARENT_OBSERVATIONS
            )
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
        engine.ledger.bump(
            _reverse_add_keys.TILE_CAUSAL_FINITE_TRANSFER_PARENT_OBSERVATIONS
        )
    engine.ledger.bump(_reverse_add_keys.TILE_CAUSAL_FINITE_PAIR_TRANSFERS)
    return state


__all__ = ["ReverseAddFinitePairTransfer", "ReverseAddFinitePairTransferFactory"]
