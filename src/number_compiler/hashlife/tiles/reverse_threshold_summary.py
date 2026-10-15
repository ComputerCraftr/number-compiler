"""Canonical reverse/add threshold summaries over exact tile identities.

The summary is the LT/EQ/GT carry-reset monoid for the active pair prefix.  It
is built parent-first from canonical child summaries and retained in the shared
completed-result memo.  No carry row, digit word, or coordinate scan is used.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.formula.summary import (
    BlockSummary,
    compose_summaries,
    summary_from_values,
)
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.tiles.result_reverse_indexes import publish_indexed_result
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import (
    ReverseThresholdSummaryKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.result_cache_kinds import (
    ResultCacheKind,
    record_unattributed_post_eviction_miss,
)
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )


@dataclass(frozen=True, slots=True)
class _SummaryFrame:
    """One charged iterative visit in the scheduler's existing frame store."""

    args: tuple[TileID]
    ready: bool = False
    known_missing: bool = False
    saved: tuple[()] = ()


class _UnsupportedReverseShape(ValueError):
    """The threshold shortcut cannot summarize this otherwise valid source."""


def _validate_key(
    results: CompletedResultArena,
    key: ReverseThresholdSummaryKey,
) -> None:
    if type(results) is not CompletedResultArena:
        raise TypeError("reverse summaries require the shared result arena")
    if type(key) is not ReverseThresholdSummaryKey:
        raise TypeError("reverse summary has another key sort")
    key.__post_init__()
    node = results.tiles.resolve(key.input)
    alphabet = results.tiles.alphabet(node.alphabet)
    if (
        alphabet.radix != key.base
        or alphabet.blank != 2 * key.base - 1
        or alphabet.symbol_count != 2 * key.base
        or alphabet.interpretation != "unsigned-radix-cell-with-explicit-blank"
        or alphabet.version != CANONICAL_TILE_ALPHABET_VERSION
    ):
        raise ValueError("tile alphabet is not a canonical reverse pair field")


def _lookup(
    results: CompletedResultArena,
    key: ReverseThresholdSummaryKey,
) -> BlockSummary | None:
    _validate_key(results, key)
    found = results._memo.get(key)
    results.ledger.bump(_tiles_keys.REVERSE_THRESHOLD_SUMMARY_REQUESTS)
    if found is None:
        record_unattributed_post_eviction_miss(
            results.ledger, ResultCacheKind.INTERFACE
        )
        return None
    if type(found) is not BlockSummary:
        raise TypeError("reverse threshold memo contains another value sort")
    if found.length != results.tiles.resolve(key.input).extent:
        raise ValueError("reverse threshold summary lost its active extent")
    results.ledger.bump(_tiles_keys.REVERSE_THRESHOLD_SUMMARY_EARLY_HITS)
    return found


def _publish(
    results: CompletedResultArena,
    key: ReverseThresholdSummaryKey,
    summary: BlockSummary,
) -> BlockSummary:
    _validate_key(results, key)
    if type(summary) is not BlockSummary:
        raise TypeError("reverse threshold publication requires a BlockSummary")
    summary.__post_init__()
    if summary.length != results.tiles.resolve(key.input).extent:
        raise ValueError("reverse threshold summary has another active extent")
    found = results._memo.get(key)
    results.ledger.bump(_tiles_keys.REVERSE_THRESHOLD_SUMMARY_PUBLICATION_REQUESTS)
    if found is not None:
        if type(found) is not BlockSummary or found != summary:
            raise ValueError("reverse threshold tile already has another summary")
        results.ledger.bump(_tiles_keys.REVERSE_THRESHOLD_SUMMARY_LATE_DUPLICATES)
        return found
    publish_indexed_result(results, key, summary)
    results.ledger.bump(_tiles_keys.REVERSE_THRESHOLD_SUMMARY_PUBLICATIONS)
    return summary


def reverse_threshold_summary(
    results: CompletedResultArena,
    tile: TileID,
    base: int,
) -> BlockSummary:
    """Return the active prefix's carry-reset summary without visiting positions."""
    root_key = ReverseThresholdSummaryKey(tile, base)
    cached = _lookup(results, root_key)
    if cached is not None:
        return cached
    tasks = results._causal_tasks
    if tasks is None:
        raise ValueError("reverse summaries require the scheduler workspace")
    frames = tasks.frames
    initial_depth = len(frames)
    # The public root probe above authenticated the request and proved this
    # exact key absent.  A child has lower level and cannot publish its parent,
    # so the fact stays valid until this synchronous frame publishes the root.
    frames.append(_SummaryFrame((tile,), known_missing=True))
    spec = RadixSpec(base)
    try:
        while len(frames) > initial_depth:
            frame = frames.pop()
            if type(frame) is not _SummaryFrame:
                raise TypeError("reverse summary workspace contains another task sort")
            current, ready = frame.args[0], frame.ready
            node = results.tiles.resolve(current)
            if node.first_active is None:
                continue
            key = ReverseThresholdSummaryKey(current, base)
            if frame.known_missing:
                results.ledger.bump(
                    _tiles_keys.REVERSE_THRESHOLD_SUMMARY_KNOWN_MISSING_PROBE_ELISIONS
                )
            elif _lookup(results, key) is not None:
                continue
            if not node.level:
                if node.symbol is None or node.symbol == 2 * base - 1:
                    raise ValueError("active reverse leaf omitted its pair symbol")
                summary = summary_from_values((node.symbol,), spec)
            else:
                if node.left is None or node.right is None:
                    raise ValueError("reverse summary encountered a malformed tile")
                if not ready:
                    frames.extend(
                        (
                            _SummaryFrame((current,), True, True),
                            _SummaryFrame((node.right,)),
                            _SummaryFrame((node.left,)),
                        )
                    )
                    continue
                left_node = results.tiles.resolve(node.left)
                right_node = results.tiles.resolve(node.right)
                left = (
                    None
                    if left_node.first_active is None
                    else _lookup(results, ReverseThresholdSummaryKey(node.left, base))
                )
                right = (
                    None
                    if right_node.first_active is None
                    else _lookup(results, ReverseThresholdSummaryKey(node.right, base))
                )
                if left is None:
                    raise _UnsupportedReverseShape(
                        "reverse pair field has blank cells before activity"
                    )
                if right_node.first_active is not None and right is None:
                    raise ValueError(
                        "active reverse child omitted its threshold summary"
                    )
                summary = left if right is None else compose_summaries(left, right)
            if summary.length != node.extent:
                raise _UnsupportedReverseShape("reverse pair field has a blank gap")
            _publish(results, key, summary)
            results.ledger.bump(_tiles_keys.REVERSE_THRESHOLD_SUMMARY_EVALUATIONS)
        result = _lookup(results, root_key)
        if result is None:
            raise ValueError("reverse pair field has no active symbols")
        return result
    finally:
        while len(frames) > initial_depth:
            frames.pop()


def reverse_current_growth(
    results: CompletedResultArena,
    tile: TileID,
    base: int,
) -> int:
    """Return the exact outgoing carry of the current pair field."""
    summary = reverse_threshold_summary(results, tile, base)
    return int(summary.last_reset_sign > 0)


def observe_current_growth(
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
    wiring: ResultWiring,
    boundaries: BoundaryTileOperands,
) -> int | None:
    """Admit only one current reverse step with canonical exterior context."""
    record = adapter._action(action)
    if record.children is not None:
        return None
    kernel = adapter.kernels.kernel(record.kernel)
    if type(kernel.effect) is not BaseBlockEffect:
        return None
    if (
        ports != adapter.initial_ports(action)
        or wiring != adapter.wiring(action)
        or boundaries != BoundaryTileOperands()
    ):
        return None
    results = adapter._require_results()
    _validate_key(results, ReverseThresholdSummaryKey(source, kernel.base))
    if results.tiles.resolve(source).first_active is None:
        return None
    try:
        return reverse_current_growth(results, source, kernel.base)
    except _UnsupportedReverseShape:
        return None


__all__ = [
    "observe_current_growth",
    "reverse_current_growth",
    "reverse_threshold_summary",
]
