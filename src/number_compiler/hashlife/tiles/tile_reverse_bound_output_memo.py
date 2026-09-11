"""Canonical bounded reverse-output summaries in the shared result memo."""

from __future__ import annotations

from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.tiles.tile_result_records import ReverseBoundOutputKey
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.resources.result_cache_kinds import (
    REVERSE_BOUND_OUTPUT_RETAINED_NODES,
    record_unattributed_post_eviction_miss,
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
        or alphabet.version != "canonical-tile-alphabet-v1"
    ):
        raise ValueError("tile alphabet is not a canonical reverse pair field")
    return alphabet.radix, node.level


def lookup_reverse_bound_output(
    results: CompletedResultArena, key: ReverseBoundOutputKey
) -> ReverseBoundOutput | None:
    """Probe one exact tile summary before visiting its descendants."""
    base, _level = _validate_key(results, key)
    results.ledger.bump("reverse_bound_output_requests")
    found = results._memo.get(key)
    if found is None:
        record_unattributed_post_eviction_miss(results.ledger, "interface")
        if results.ledger.counters.get("result_cache_interface_evicted_entries", 0):
            results.ledger.bump(
                "reverse_bound_output_post_eviction_misses_attribution_unknown"
            )
        return None
    if type(found) is not ReverseBoundOutput:
        raise TypeError("reverse output memo contains another value sort")
    found.__post_init__()
    if found.left.base != base:
        raise ValueError("reverse output memo contains another radix")
    results.ledger.bump("reverse_bound_output_early_hits")
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
    results.ledger.bump("reverse_bound_output_publication_requests")
    found = results._memo.get(key)
    if found is not None:
        if type(found) is not ReverseBoundOutput or found != value:
            raise ValueError("reverse output tile already has another summary")
        results.ledger.bump("reverse_bound_output_late_duplicates")
        return found
    referenced = results._tiles_for(key, value)
    reverse_entries = results._index_entries(referenced)
    reservations = (
        (results._memo_owner, 1, REVERSE_BOUND_OUTPUT_RETAINED_NODES),
        (results._reverse_owner, reverse_entries, 0),
    )
    results.ledger.reserve_many(reservations)
    reverse_snapshot = None
    try:
        reverse_snapshot = results._reverse_snapshot(referenced, key)
        results._memo[key] = value
        for tile in referenced:
            results._add_membership(tile, key)
    except BaseException:
        results._memo.pop(key, None)
        if reverse_snapshot is not None:
            results._restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            results.ledger.release(owner, entries, nodes)
        raise
    results.ledger.bump("reverse_bound_output_publications")
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
        results.ledger.bump("reverse_bound_output_leaf_evaluations")
        results.ledger.bump("reverse_bound_output_evaluations")
        return _publish(results, key, value)
    except BaseException:
        results.ledger.bump("reverse_bound_output_failures")
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
        results.ledger.bump("reverse_bound_output_parent_compositions")
        results.ledger.bump("reverse_bound_output_evaluations")
        return _publish(results, key, value)
    except BaseException:
        results.ledger.bump("reverse_bound_output_failures")
        raise


__all__ = [
    "lookup_reverse_bound_output",
    "publish_reverse_bound_output_leaf",
    "publish_reverse_bound_output_parent",
]
