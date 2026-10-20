"""Certified constant-cycle completion for canonical Collatz tiles."""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, cast

from number_compiler.hashlife.execution.tile_clock_kernel import complete_clock_kernel
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabetID,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.sequences.collatz.physical_support import (
    PhysicalSupport,
    PhysicalSupportArena,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey


_PowerSummary = tuple[Literal["zero", "blank", "power", "invalid"], int]


def _power_of_two_exponent(
    scheduler: TileScheduler,
    source: TileID,
) -> int | None:
    """Recognize ``0**k 1 blank**`` from the canonical tile DAG.

    The summary is a four-element regular monoid. Repeated zero and blank
    subtrees are visited once, so a sparse power-of-two source takes work
    proportional to its canonical source DAG rather than its padded extent.
    """
    tiles = scheduler.tiles
    source_record = tiles.resolve(source)
    scheduler.ledger.bump(_collatz_keys.COLLATZ_POWER_TWO_SUMMARY_REQUESTS)
    # Every nontrivial power of two has a zero low bit. Reject the ordinary
    # odd Collatz case before allocating or walking the summary DAG.
    if source_record.extent > 1 and tiles.point(source, 0) != 0:
        scheduler.ledger.bump(_collatz_keys.COLLATZ_POWER_TWO_LOW_BIT_DECLINES)
        return None
    summaries: dict[TileID, _PowerSummary] = {}
    pending = [(source, False)]
    peak_pending = 1
    while pending:
        current, ready = pending.pop()
        if current in summaries:
            continue
        record = tiles.resolve(current)
        scheduler.ledger.bump(_collatz_keys.COLLATZ_POWER_TWO_SUMMARY_NODE_VISITS)
        if record.level == 0:
            if record.symbol == 0:
                summary: _PowerSummary = ("zero", 0)
            elif record.symbol == 1:
                summary = ("power", 0)
            elif record.symbol == tiles.alphabet(record.alphabet).blank:
                summary = ("blank", 0)
            else:
                summary = ("invalid", 0)
            summaries[current] = summary
            continue
        if record.left is None or record.right is None:
            raise ValueError("malformed Collatz source tile")
        if not ready:
            pending.extend(
                ((current, True), (record.right, False), (record.left, False))
            )
            peak_pending = max(peak_pending, len(pending))
            continue
        left = summaries[record.left]
        right = summaries[record.right]
        if left[0] == right[0] == "zero":
            summary = ("zero", 0)
        elif left[0] == right[0] == "blank":
            summary = ("blank", 0)
        elif left[0] == "zero" and right[0] == "power":
            summary = ("power", (1 << (record.level - 1)) + right[1])
        elif left[0] == "power" and right[0] == "blank":
            summary = left
        else:
            summary = ("invalid", 0)
        summaries[current] = summary
    scheduler.ledger.bump(
        _collatz_keys.COLLATZ_POWER_TWO_SUMMARY_PEAK_ENTRIES,
        max(
            0,
            len(summaries)
            - scheduler.ledger.counters.get(
                _collatz_keys.COLLATZ_POWER_TWO_SUMMARY_PEAK_ENTRIES, 0
            ),
        ),
    )
    scheduler.ledger.bump(
        _collatz_keys.COLLATZ_POWER_TWO_SUMMARY_PEAK_FRAMES,
        max(
            0,
            peak_pending
            - scheduler.ledger.counters.get(
                _collatz_keys.COLLATZ_POWER_TWO_SUMMARY_PEAK_FRAMES, 0
            ),
        ),
    )
    result = summaries[source]
    return result[1] if result[0] == "power" else None


def _event_weight(cycle_ticks: int) -> int:
    """Count odd events after a power of two reaches cycle phase one."""
    return (cycle_ticks + 2) // 3


def _cycle_support(scheduler: TileScheduler, entry: int, cycle: int) -> PhysicalSupport:
    """Construct the proved E**entry (O E E)**q prefix in temporal order."""
    arena = cast(PhysicalSupportArena, scheduler.physical_supports)
    return arena.proved_collatz_power_two_tail(entry, cycle)


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
    """Publish a proved power-of-two tail and cycle without deep execution."""
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
    entry_ticks = _power_of_two_exponent(scheduler, key.input)
    if entry_ticks is None or ticks < entry_ticks:
        return None
    primitive_index = adapter._action_keys.get(
        ("power", action.kernel, 1, TemporalCocycle(1))
    )
    if type(primitive_index) is not int:
        raise ValueError("Collatz cycle action has no canonical primitive")
    primitive = adapter.scoped_handle(primitive_index)
    cycle_ticks = ticks - entry_ticks
    reduced_ticks = cycle_ticks % 3 or 3
    reduced = adapter.power(primitive, reduced_ticks)
    input_record = scheduler.tiles.resolve(key.input)
    compact = _compact_cycle_tile(scheduler.tiles, input_record.alphabet, 1)
    try:
        reduced_result = complete_clock_kernel(scheduler, reduced, compact.tile)
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
                    _event_weight(cycle_ticks),
                    result.frame_shift,
                    result.relative_origin,
                    scheduler.tiles.resolve(output.tile).extent,
                    observed_input_ports=result.observed_input_ports,
                    physical_support=_cycle_support(
                        scheduler, entry_ticks, cycle_ticks
                    ),
                )
                scheduler.ledger.bump(_collatz_keys.TILE_COLLATZ_CYCLE_COMPLETIONS)
                if entry_ticks:
                    scheduler.ledger.bump(_collatz_keys.TILE_COLLATZ_POWER_TWO_ENTRIES)
                scheduler.ledger.bump(
                    _shared_keys.CAUSAL_EXTENT_DISCHARGED_BY_BEHAVIOR,
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
