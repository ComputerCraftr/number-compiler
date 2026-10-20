"""Canonical bounded reverse-output summaries in the shared result memo."""

from __future__ import annotations

from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.tiles.tile_result_records import ReverseBoundOutputKey
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.result_cache_kinds import (
    REVERSE_BOUND_OUTPUT_RETAINED_NODES,
    ResultCacheKind,
    record_unattributed_post_eviction_miss,
)
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)


def _validate_key(
    results: CompletedResultArena, key: ReverseBoundOutputKey
) -> tuple[int, int]:
    if type(results) is not CompletedResultArena:
        raise TypeError("reverse output summaries require the shared result arena")
    if type(key) is not ReverseBoundOutputKey:
        raise TypeError("reverse output summary has another key sort")
    key.__post_init__()
    node = results.tiles.resolve(key.input)
    alphabet = results.tiles.alphabet(node.alphabet)
    if (
        alphabet.blank != 2 * alphabet.radix - 1
        or alphabet.symbol_count != 2 * alphabet.radix
        or alphabet.interpretation != "unsigned-radix-cell-with-explicit-blank"
        or alphabet.version != CANONICAL_TILE_ALPHABET_VERSION
    ):
        raise ValueError("tile alphabet is not a canonical reverse pair field")
    return alphabet.radix, node.level


def lookup_reverse_bound_output(
    results: CompletedResultArena, key: ReverseBoundOutputKey
) -> ReverseBoundOutput | None:
    """Probe one exact tile summary before visiting its descendants."""
    base, _level = _validate_key(results, key)
    results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_REQUESTS)
    found = results.memo_view.get(key)
    if found is None:
        record_unattributed_post_eviction_miss(
            results.ledger, ResultCacheKind.INTERFACE
        )
        if results.ledger.counters.get(
            _tiles_keys.RESULT_CACHE_INTERFACE_EVICTED_ENTRIES, 0
        ):
            results.ledger.bump(
                _tiles_keys.REVERSE_BOUND_OUTPUT_POST_EVICTION_MISSES_ATTRIBUTION_UNKNOWN
            )
        return None
    if type(found) is not ReverseBoundOutput:
        raise TypeError("reverse output memo contains another value sort")
    found.__post_init__()
    if found.left.base != base:
        raise ValueError("reverse output memo contains another radix")
    results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_EARLY_HITS)
    return found


def _publish(
    results: CompletedResultArena,
    key: ReverseBoundOutputKey,
    value: ReverseBoundOutput,
) -> ReverseBoundOutput:
    base, _level = _validate_key(results, key)
    if type(value) is not ReverseBoundOutput:
        raise TypeError("reverse output publication has another value sort")
    value.__post_init__()
    if value.left.base != base:
        raise ValueError("reverse output publication has another radix")
    results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_PUBLICATION_REQUESTS)
    found = results.memo_view.get(key)
    if found is not None:
        if type(found) is not ReverseBoundOutput or found != value:
            raise ValueError("reverse output tile already has another summary")
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_LATE_DUPLICATES)
        return found
    referenced = results.tiles_for(key, value)
    reverse_entries = results.index_entries(referenced)
    reservations = (
        (results.memo_owner, 1, REVERSE_BOUND_OUTPUT_RETAINED_NODES),
        (results.reverse_owner, reverse_entries, 0),
    )
    results.ledger.reserve_many(reservations)
    reverse_snapshot = None
    try:
        reverse_snapshot = results.reverse_snapshot(referenced, key)
        results.write_memo_reserved(key, value)
        for tile in referenced:
            results.add_membership(tile, key)
    except BaseException:
        results.discard_memo(key)
        if reverse_snapshot is not None:
            results.restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            results.ledger.release(owner, entries, nodes)
        raise
    results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_PUBLICATIONS)
    return value


def publish_reverse_bound_output_leaf(
    results: CompletedResultArena, key: ReverseBoundOutputKey
) -> ReverseBoundOutput:
    """Construct and publish the only valid summary for one exact leaf."""
    base, level = _validate_key(results, key)
    try:
        node = results.tiles.resolve(key.input)
        if level or node.symbol is None:
            raise ValueError("reverse output leaf publication requires an exact leaf")
        value = ReverseBoundOutput.leaf(base, node.symbol)
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_LEAF_EVALUATIONS)
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_EVALUATIONS)
        return _publish(results, key, value)
    except BaseException:
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_FAILURES)
        raise


def publish_reverse_bound_output_parent(
    results: CompletedResultArena,
    key: ReverseBoundOutputKey,
    left: ReverseBoundOutput,
    right: ReverseBoundOutput,
) -> ReverseBoundOutput:
    """Compose and publish one parent from its exact completed children."""
    _base, level = _validate_key(results, key)
    try:
        node = results.tiles.resolve(key.input)
        if not level or node.left is None or node.right is None:
            raise ValueError(
                "reverse output parent publication requires exact children"
            )
        if (
            lookup_reverse_bound_output(results, ReverseBoundOutputKey(node.left))
            != left
            or lookup_reverse_bound_output(results, ReverseBoundOutputKey(node.right))
            != right
        ):
            raise ValueError(
                "reverse output parent differs from its completed children"
            )
        value = left.then(right, results.ledger)
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_PARENT_COMPOSITIONS)
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_EVALUATIONS)
        return _publish(results, key, value)
    except BaseException:
        results.ledger.bump(_tiles_keys.REVERSE_BOUND_OUTPUT_FAILURES)
        raise


__all__ = [
    "lookup_reverse_bound_output",
    "publish_reverse_bound_output_leaf",
    "publish_reverse_bound_output_parent",
]
