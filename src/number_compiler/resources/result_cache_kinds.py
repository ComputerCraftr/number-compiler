"""Bounded cache-kind accounting without retaining request tombstones."""

from __future__ import annotations

from collections.abc import Iterable
from enum import StrEnum

from number_compiler.arithmetic.contracts.input_validation import (
    is_runtime_instance,
)
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
from number_compiler.resources.metric_keys import resources as _resources_keys


class ResultCacheKind(StrEnum):
    RESULT = "result"
    INTERFACE = "interface"
    BEHAVIOR = "behavior"
    REGION = "region"
    SPATIAL = "spatial"


class RemovalCause(StrEnum):
    EVICTION = "eviction"
    RETIREMENT = "retirement"


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
        return ResultCacheKind.RESULT
    if type(key) in (
        PoweredInterfaceKey,
        FusedInterfaceKey,
        CausalInterfaceKey,
        DirectedTransferKey,
        ReverseThresholdSummaryKey,
        ReverseBoundOutputKey,
        SourceRootMatchKey,
    ):
        return ResultCacheKind.INTERFACE
    if type(key) is BehaviorBindingKey:
        return ResultCacheKind.BEHAVIOR
    if type(key) in (NormalizedRegionKey, BoundaryConcatKey):
        return ResultCacheKind.REGION
    if type(key) is SpatialInterfaceKey:
        return ResultCacheKind.SPATIAL
    raise TypeError("shared result memo contains an unknown key sort")


def record_cache_removal(
    ledger: ResourceLedger,
    key: object,
    cause: RemovalCause,
) -> None:
    """Attribute one removed entry while retaining no semantic request history."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("cache removal accounting requires an index ledger")
    if not is_runtime_instance(cause, RemovalCause):
        raise TypeError("cache removal accounting has another cause")
    kind = result_cache_kind(key)
    ledger.bump(_resources_keys.RESULT_CACHE_KIND_CLASSIFICATION_VISITS)
    suffix = (
        "evicted_entries" if cause is RemovalCause.EVICTION else "retirement_removals"
    )
    ledger.bump(f"result_cache_{kind}_{suffix}")
    if type(key) is ReverseBoundOutputKey and cause is RemovalCause.EVICTION:
        ledger.bump(_resources_keys.REVERSE_BOUND_OUTPUT_EVICTIONS)


def record_unattributed_post_eviction_miss(
    ledger: ResourceLedger,
    kind: ResultCacheKind,
) -> None:
    """Count an unknown-attribution miss only after this cache kind was evicted."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("cache miss accounting requires an index ledger")
    if not is_runtime_instance(kind, ResultCacheKind):
        raise TypeError("cache miss accounting has another bounded kind")
    if ledger.counters.get(f"result_cache_{kind}_evicted_entries", 0):
        ledger.bump(f"result_cache_{kind}_post_eviction_misses_attribution_unknown")
        if kind is ResultCacheKind.RESULT:
            ledger.bump(
                _resources_keys.COMPLETED_RESULT_RECOMPUTATION_ATTRIBUTION_UNKNOWN
            )


__all__ = [
    "REVERSE_BOUND_OUTPUT_RETAINED_NODES",
    "record_cache_removal",
    "record_unattributed_post_eviction_miss",
    "result_cache_kind",
    "retained_result_memo_nodes",
]
