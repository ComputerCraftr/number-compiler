"""Bounded cache-kind accounting without retaining request tombstones."""

from __future__ import annotations

from collections.abc import Iterable
from typing import Literal

from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    BoundaryConcatKey,
    CausalInterfaceKey,
    CompletedInterfaceResult,
    DirectedTransferKey,
    FusedInterfaceKey,
    NormalizedRegionKey,
    PoweredInterfaceKey,
    PoweredResultKey,
    ReverseBoundOutputKey,
    ReverseThresholdSummaryKey,
    SourceRootMatchKey,
    SpatialInterfaceKey,
)
from number_compiler.resources.ledger import ResourceLedger

ResultCacheKind = Literal["result", "interface", "behavior", "region", "spatial"]
RemovalCause = Literal["eviction", "retirement"]
REVERSE_BOUND_OUTPUT_RETAINED_NODES = 9


def retained_result_memo_nodes(values: Iterable[object]) -> int:
    """Count inline bounded payload slots retained by the shared result memo."""
    return sum(
        value.retained_nodes
        if type(value) is CompletedInterfaceResult
        else REVERSE_BOUND_OUTPUT_RETAINED_NODES
        if type(value) is ReverseBoundOutput
        else 0
        for value in values
    )


def result_cache_kind(key: object) -> ResultCacheKind:
    """Classify every admitted shared-result key by its semantic cache level."""
    if type(key) is PoweredResultKey:
        return "result"
    if type(key) in (
        PoweredInterfaceKey,
        FusedInterfaceKey,
        CausalInterfaceKey,
        DirectedTransferKey,
        ReverseThresholdSummaryKey,
        ReverseBoundOutputKey,
        SourceRootMatchKey,
    ):
        return "interface"
    if type(key) is BehaviorBindingKey:
        return "behavior"
    if type(key) in (NormalizedRegionKey, BoundaryConcatKey):
        return "region"
    if type(key) is SpatialInterfaceKey:
        return "spatial"
    raise TypeError("shared result memo contains an unknown key sort")


def record_cache_removal(
    ledger: ResourceLedger,
    key: object,
    cause: RemovalCause,
) -> None:
    """Attribute one removed entry while retaining no semantic request history."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("cache removal accounting requires an index ledger")
    if cause not in ("eviction", "retirement"):
        raise ValueError("cache removal accounting has another cause")
    kind = result_cache_kind(key)
    ledger.bump("result_cache_kind_classification_visits")
    suffix = "evicted_entries" if cause == "eviction" else "retirement_removals"
    ledger.bump(f"result_cache_{kind}_{suffix}")
    if type(key) is ReverseBoundOutputKey and cause == "eviction":
        ledger.bump("reverse_bound_output_evictions")


def record_unattributed_post_eviction_miss(
    ledger: ResourceLedger,
    kind: ResultCacheKind,
) -> None:
    """Count an unknown-attribution miss only after this cache kind was evicted."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("cache miss accounting requires an index ledger")
    if kind not in ("result", "interface", "behavior", "region", "spatial"):
        raise ValueError("cache miss accounting has another bounded kind")
    if ledger.counters.get(f"result_cache_{kind}_evicted_entries", 0):
        ledger.bump(f"result_cache_{kind}_post_eviction_misses_attribution_unknown")
        if kind == "result":
            ledger.bump("completed_result_recomputation_attribution_unknown")


__all__ = [
    "REVERSE_BOUND_OUTPUT_RETAINED_NODES",
    "record_cache_removal",
    "record_unattributed_post_eviction_miss",
    "retained_result_memo_nodes",
    "result_cache_kind",
]
