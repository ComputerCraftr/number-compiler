"""Complete a proved initial Collatz root run with two primitive scans."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.tile_clock_kernel import complete_clock_kernel
from number_compiler.hashlife.execution.tile_collatz_root import initial_event_shift
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
    concat_boundary_views,
)
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey


def _shift_right_with_blank(
    tiles: TileArena,
    source: TileID,
    shift: int,
) -> TileLease:
    """Return a fixed-width logical right shift by reusing dyadic subtrees."""
    node = tiles.resolve(source)
    if type(shift) is not int:
        raise TypeError("tile shift requires an exact integer")
    if not 0 <= shift <= node.width:
        raise ValueError("tile shift lies outside its source")
    if not shift:
        return tiles.retain(source)
    alphabet = node.alphabet
    blank_symbol = tiles.alphabet(alphabet).blank
    blank = tiles.leaf(alphabet, blank_symbol)
    try:
        while tiles.resolve(blank.tile).level < node.level:
            parent = tiles.join(blank.tile, blank.tile)
            blank.close()
            blank = parent
        suffix = None
        if shift < node.width:
            suffix = BoundaryTileView(
                source,
                0,
                node.width - shift,
                0,
                shift,
            )
        padding = BoundaryTileView(blank.tile, 0, shift)
        _view, result = concat_boundary_views(tiles, alphabet, suffix, padding)
        if result is None or tiles.resolve(result.tile).level != node.level:
            if result is not None:
                result.close()
            raise AssertionError("fixed-width tile shift lost its root")
        tiles.ledger.bump("collatz_initial_root_structural_shifts")
        return result
    finally:
        blank.close()


def complete_collatz_root(
    scheduler: TileScheduler,
    key: PoweredResultKey,
) -> ResultLease | None:
    """Publish a complete result while still inside the first odd event.

    The root matcher proves that every middle physical tick is division by two.
    One primitive scan constructs ``3*x+1``.  A structural shift skips all but
    the final division, whose primitive scan supplies the exact outgoing
    interface and boundary metadata required by a reusable completed result.
    """
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    admitted = initial_event_shift(scheduler, key)
    if admitted is None:
        return None
    primitive, shift = admitted
    if shift < 2:
        raise AssertionError("initial root completion requires a middle division")
    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise AssertionError("root admission returned another tile adapter")
    first = complete_clock_kernel(scheduler, primitive, key.input)
    try:
        first_value = first.result
        if (
            first_value.physical_ticks != 1
            or first_value.event_weight != 1
            or first_value.frame_shift
        ):
            raise ValueError("initial odd primitive returned invalid Collatz metadata")
        penultimate = _shift_right_with_blank(
            scheduler.tiles,
            first_value.output,
            shift - 1,
        )
        try:
            final = complete_clock_kernel(scheduler, primitive, penultimate.tile)
            try:
                value = final.result
                if (
                    value.physical_ticks != 1
                    or value.event_weight
                    or value.frame_shift
                    or value.fusion is not None
                ):
                    raise ValueError(
                        "final even primitive returned invalid Collatz metadata"
                    )
                ticks = adapter.action_cocycle(key.action).physical_ticks
                output_node = scheduler.tiles.resolve(value.output)
                outgoing_boundaries = BoundaryTileOperands(
                    BoundaryTileView(value.output, 0, output_node.width),
                    BoundaryTileView(value.output, 0, output_node.width, 1),
                )
                support_arena = scheduler.physical_supports
                physical_support = support_arena.concat(
                    support_arena.odd,
                    support_arena.run(False, ticks - 1),
                )
                completed = CompletedResult(
                    value.output,
                    value.outgoing,
                    value.outgoing_ports,
                    ticks,
                    1,
                    value.frame_shift,
                    value.relative_origin,
                    value.relative_extent,
                    outgoing_boundaries,
                    value.fusion,
                    key.ports,
                    physical_support,
                )
                scheduler.ledger.bump("tile_collatz_initial_root_completions")
                scheduler.ledger.bump(
                    "collatz_initial_root_skipped_ticks",
                    shift - 1,
                )
                return scheduler.results.publish(key, completed)
            finally:
                final.close()
        finally:
            penultimate.close()
    finally:
        first.close()


__all__ = ["complete_collatz_root"]
