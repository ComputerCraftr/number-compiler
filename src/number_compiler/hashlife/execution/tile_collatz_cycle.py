"""Certified constant-cycle completion for canonical Collatz tiles."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabetID,
    TileArena,
    TileID,
    TileLease,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey


def _cycle_source(scheduler: TileScheduler, key: PoweredResultKey) -> int | None:
    record = scheduler.tiles.resolve(key.input)
    if not 1 <= record.extent <= 3:
        return None
    value = 0
    for coordinate in range(record.extent):
        symbol = scheduler.tiles.point(key.input, coordinate)
        if symbol not in (0, 1):
            return None
        value |= symbol << coordinate
    return value if value in (1, 2, 4) else None


def _event_weight(source: int, ticks: int) -> int:
    if source == 1:
        return (ticks + 2) // 3
    if source == 2:
        return (ticks + 1) // 3
    if source == 4:
        return ticks // 3
    raise AssertionError("unrecognized Collatz cycle source")


def _compact_cycle_tile(
    tiles: TileArena,
    alphabet: TileAlphabetID,
    value: int,
) -> TileLease:
    leaves: list[TileLease] = []
    try:
        for coordinate in range(8):
            symbol = (value >> coordinate) & 1 if value >> coordinate else 2
            leaves.append(tiles.leaf(alphabet, symbol))
        while len(leaves) > 1:
            parents: list[TileLease] = []
            for index in range(0, len(leaves), 2):
                parents.append(tiles.join(leaves[index].tile, leaves[index + 1].tile))
                leaves[index].close()
                leaves[index + 1].close()
            leaves = parents
        return leaves.pop()
    except BaseException:
        for leaf in leaves:
            leaf.close()
        raise


def _extend_with_blank(
    tiles: TileArena,
    output: TileID,
    target_level: int,
) -> TileLease:
    current = tiles.retain(output)
    record = tiles.resolve(current.tile)
    alphabet = record.alphabet
    blank_symbol = tiles.alphabet(alphabet).blank
    blank = tiles.leaf(alphabet, blank_symbol)
    try:
        while tiles.resolve(blank.tile).level < record.level:
            parent = tiles.join(blank.tile, blank.tile)
            blank.close()
            blank = parent
        while tiles.resolve(current.tile).level < target_level:
            parent = tiles.join(current.tile, blank.tile)
            current.close()
            current = parent
            blank_parent = tiles.join(blank.tile, blank.tile)
            blank.close()
            blank = blank_parent
        return current
    except BaseException:
        current.close()
        raise
    finally:
        blank.close()


def complete_collatz_cycle(
    scheduler: TileScheduler,
    key: PoweredResultKey,
) -> ResultLease | None:
    """Publish a proved ``1 -> 4 -> 2 -> 1`` result without deep execution."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.sequences.collatz.block_power import (
        CollatzPhysicalBlockEffect,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    action = adapter._action(key.action)
    kernel = adapter.kernels.kernel(action.kernel)
    ticks = action.cocycle.physical_ticks
    if (
        type(kernel.effect) is not CollatzPhysicalBlockEffect
        or not action.homogeneous
        or action.cocycle != TemporalCocycle(ticks)
        or ticks <= 3
        or key.fusion is not None
        or key.region is not None
        or key.boundaries.tile_ids()
        or key.ports != adapter.initial_ports(key.action)
        or key.wiring != adapter.wiring(key.action)
    ):
        return None
    source = _cycle_source(scheduler, key)
    if source is None:
        return None
    primitive_index = adapter._action_keys.get(
        ("power", action.kernel, 1, TemporalCocycle(1))
    )
    if type(primitive_index) is not int:
        raise ValueError("Collatz cycle action has no canonical primitive")
    primitive = adapter._handle(primitive_index)
    reduced_ticks = ticks % 3 or 3
    reduced = adapter.power(primitive, reduced_ticks)
    input_record = scheduler.tiles.resolve(key.input)
    compact = _compact_cycle_tile(scheduler.tiles, input_record.alphabet, source)
    try:
        reduced_result = scheduler.complete(
            reduced,
            compact.tile,
            adapter.initial_ports(reduced),
            adapter.wiring(reduced),
        )
        try:
            result = reduced_result.result
            output = _extend_with_blank(
                scheduler.tiles,
                result.output,
                input_record.level,
            )
            try:
                completed = CompletedResult(
                    output.tile,
                    result.outgoing,
                    result.outgoing_ports,
                    ticks,
                    _event_weight(source, ticks),
                    result.frame_shift,
                    result.relative_origin,
                    scheduler.tiles.resolve(output.tile).extent,
                    observed_input_ports=result.observed_input_ports,
                )
                scheduler.ledger.bump("tile_collatz_cycle_completions")
                scheduler.ledger.bump(
                    "causal_extent_discharged_by_behavior",
                    input_record.width,
                )
                return scheduler.results.publish(key, completed)
            finally:
                output.close()
        finally:
            reduced_result.close()
    finally:
        compact.close()


__all__ = ["complete_collatz_cycle"]
