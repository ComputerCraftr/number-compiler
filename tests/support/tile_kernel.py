"""Primitive bimachines execute through canonical tiles and finite interfaces."""

from __future__ import annotations

from collections.abc import Sequence

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import (
    ChildContext,
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import (
    TileArena,
    TileID,
    TileLease,
    TileRecord,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_family_hooks import collatz_tile_hooks
from number_compiler.sequences.reverse_add.tile_pair_transfer import (
    ReverseAddFinitePairTransferFactory,
)


def make_tile_runtime(
    effect: BlockEffect,
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
]:
    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    interfaces = DiamondQuotientArena(SemanticFunctionArena(ledger))
    tiles = TileArena(ledger)
    hooks = collatz_tile_hooks() if type(effect) is CollatzPhysicalBlockEffect else None
    # BaseBlockEffect names the reverse/add family at every radix. Its
    # decimal-only morphism is an internal strategy branch, not its admission.
    pair_transfer_factory = (
        ReverseAddFinitePairTransferFactory()
        if type(effect) is BaseBlockEffect
        else None
    )
    pair_transfer = (
        None if pair_transfer_factory is None else pair_transfer_factory.create(ledger)
    )
    adapter = PrimitiveTileKernelAdapter(
        tiles,
        kernels,
        interfaces,
        family_hooks=hooks,
        pair_transfer=pair_transfer,
    )
    action = adapter.admit(effect)
    results = CompletedResultArena(
        tiles,
        interfaces,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    return ledger, tiles, adapter, action, TileScheduler(tiles, results, adapter)


def make_tile_from_symbols(
    tiles: TileArena,
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    symbols: tuple[int, ...],
) -> TileLease:
    if not symbols or len(symbols) & (len(symbols) - 1):
        raise ValueError("test tile width must be a power of two")
    level = [tiles.leaf(adapter.alphabet(action), symbol) for symbol in symbols]
    try:
        while len(level) > 1:
            following = [
                tiles.join(level[index].tile, level[index + 1].tile)
                for index in range(0, len(level), 2)
            ]
            for lease in level:
                lease.close()
            level = following
        return level.pop()
    except BaseException:
        for lease in level:
            lease.close()
        raise


def literal_tile_output(
    effect: BlockEffect,
    symbols: tuple[int, ...],
) -> tuple[int, ...]:
    left = effect.initial(BoundarySide.LEFT)
    left_states = []
    for symbol in symbols:
        left_states.append(left)
        left = effect.advance(BoundarySide.LEFT, left, symbol)
    right = effect.initial(BoundarySide.RIGHT)
    right_states = [right] * len(symbols)
    for index in range(len(symbols) - 1, -1, -1):
        right_states[index] = right
        right = effect.advance(BoundarySide.RIGHT, right, symbols[index])
    return tuple(
        int(effect.emit(left_state, symbol, right_state))
        for left_state, symbol, right_state in zip(
            left_states,
            symbols,
            right_states,
            strict=True,
        )
    )


def read_tile_symbols(tiles: TileArena, tile: TileID) -> tuple[int, ...]:
    return tuple(
        tiles.point(tile, coordinate) for coordinate in range(tiles.resolve(tile).width)
    )


def make_tile_runtime_source(
    effect: BlockEffect, symbols: tuple[int, ...]
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
    TileLease,
]:
    """Construct and retain the exact input tile in the shared kernel fixture."""
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(effect)
    source = make_tile_from_symbols(tiles, adapter, primitive, symbols)
    return ledger, tiles, adapter, primitive, scheduler, source


def runtime_tile_inputs(
    tiles: TileArena,
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    source: TileLease,
) -> tuple[TileRecord, TileID, TileID, tuple[int, ...], ResultWiring]:
    node = tiles.resolve(source.tile)
    assert node.left is not None and node.right is not None
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    return node, node.left, node.right, ports, wiring


def runtime_spatial_inputs(
    tiles: TileArena,
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    source: TileLease,
) -> tuple[
    TileRecord,
    TileID,
    TileID,
    tuple[int, ...],
    ResultWiring,
    ChildContext,
    ChildContext,
]:
    node, left, right, ports, wiring = runtime_tile_inputs(
        tiles, adapter, action, source
    )
    left_context = adapter.child_context(
        action, source.tile, left, right, ports, wiring, 0
    )
    right_context = adapter.child_context(
        action, source.tile, left, right, ports, wiring, 1
    )
    return node, left, right, ports, wiring, left_context, right_context


def join_four(
    tiles: TileArena, leaves: Sequence[TileLease]
) -> tuple[TileLease, TileLease, TileLease]:
    left = tiles.join(leaves[0].tile, leaves[1].tile)
    right = tiles.join(leaves[2].tile, leaves[3].tile)
    root = tiles.join(left.tile, right.tile)
    return left, right, root


def powered_runtime_source(
    effect: BlockEffect, symbols: tuple[int, ...], exponent: int
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
    TileLease,
    FieldCellActionID,
]:
    ledger, tiles, adapter, primitive, scheduler, source = make_tile_runtime_source(
        effect, symbols
    )
    action = adapter.power(primitive, exponent)
    return ledger, tiles, adapter, primitive, scheduler, source, action


def runtime_signature(
    effect: BlockEffect,
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
    tuple[int, ...],
    ResultWiring,
]:
    ledger, tiles, adapter, action, scheduler = make_tile_runtime(effect)
    ports = adapter.initial_ports(action)
    wiring = adapter.wiring(action)
    return ledger, tiles, adapter, action, scheduler, ports, wiring


def powered_runtime(
    effect: BlockEffect, exponent: int
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
    FieldCellActionID,
    int,
]:
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(effect)
    action = adapter.power(primitive, exponent)
    blank = adapter.primitive_law(primitive).blank
    return ledger, tiles, adapter, primitive, scheduler, action, blank


def runtime_source_children(
    effect: BlockEffect, symbols: tuple[int, ...]
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
    TileLease,
    TileRecord,
]:
    ledger, tiles, adapter, primitive, scheduler, source = make_tile_runtime_source(
        effect, symbols
    )
    node = tiles.resolve(source.tile)
    assert node.left is not None and node.right is not None
    return ledger, tiles, adapter, primitive, scheduler, source, node


def powered_application(
    projection: LazyProjection,
    steps: int = 4,
) -> tuple[PrimitiveTileKernelAdapter, FieldCellActionID, TileApplication]:
    primitive = projection._application
    adapter = primitive.scheduler.adapter
    assert type(adapter) is PrimitiveTileKernelAdapter
    action = adapter.power(primitive.action, steps)
    application = primitive.scheduler.application(
        action,
        primitive.source,
        adapter.initial_ports(action),
        adapter.wiring(action),
    )
    return adapter, action, application
