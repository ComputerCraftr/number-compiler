"""Cache distributions and retirement work report actual runtime events."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    lookup_causal_interface,
    publish_causal_interface,
)
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.resources.cache_gc_metrics import MAX_CACHE_EVENT_BUCKETS
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.ownership import (
    audit_execution_ownership as _canonical_audit_execution_ownership,
)
from tests.resources.test_tile_causal_interface_memo import _binding
from tests.support.tile_results import _setup

if TYPE_CHECKING:
    from number_compiler.resources.ownership import OwnershipAudit


def test_metric_projection_rejects_a_mixed_live_cache_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.resources.metric_collection as collection

    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    tiles._cache_metrics.record(
        "tile",
        "publication",
        spatial_level=0,
        temporal_span=None,
    )
    ordinary = _canonical_audit_execution_ownership

    def mutate_after_capture(
        selected: ResourceLedger, *, fresh: bool = True
    ) -> OwnershipAudit:
        result = ordinary(selected, fresh=fresh)
        key = next(iter(tiles._cache_metrics.buckets))
        tiles._cache_metrics.buckets[key] += 1
        return result

    monkeypatch.setattr(collection, "audit_execution_ownership", mutate_after_capture)
    with pytest.raises(RuntimeError, match="changed during metric projection"):
        collect_ledger_metrics(ledger)


def test_metric_projection_rejects_counter_work_after_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.resources.metric_collection as collection

    ledger = ResourceLedger()
    ordinary = _canonical_audit_execution_ownership

    def mutate_counter(
        selected: ResourceLedger, *, fresh: bool = True
    ) -> OwnershipAudit:
        result = ordinary(selected, fresh=fresh)
        ledger.bump("injected_reporting_work")
        return result

    monkeypatch.setattr(collection, "audit_execution_ownership", mutate_counter)
    with pytest.raises(RuntimeError, match="changed during metric projection"):
        collect_ledger_metrics(ledger)


def test_result_hits_are_distributed_by_spatial_level_and_temporal_span() -> None:
    ledger, _actions, _tiles, results, input_lease, output_lease, key, result = _setup()
    held = None
    warm = None
    try:
        assert results.lookup(key) is None
        held = results.publish(key, result)
        warm = results.lookup(key)
        assert warm is not None
        before = ledger.snapshot()
        metrics = collect_ledger_metrics(ledger)
        assert ledger.snapshot() == before
        assert metrics.cache_events_by_spatial_level == {
            "result:early_hit:0": 1,
            "result:miss:0": 1,
            "result:publication:0": 1,
            "tile:publication:0": 2,
        }
        # This test authority intentionally has no temporal cocycle method.
        assert metrics.cache_events_by_temporal_span == {}
    finally:
        if warm is not None:
            warm.close()
        if held is not None:
            held.close()
        output_lease.close()
        input_lease.close()


def test_tile_retirement_reports_gc_deltas_and_unknown_recreation() -> None:
    ledger, _actions, tiles, _results, input_lease, output_lease, key, _result = (
        _setup()
    )
    alphabet = tiles.resolve(key.input).alphabet
    output_lease.close()
    input_lease.close()
    recreated = tiles.leaf(alphabet, 1)
    try:
        metrics = collect_ledger_metrics(ledger)
        assert metrics.tile_retirements >= 2
        assert metrics.tile_retirement_work_ns > 0
        assert metrics.python_gc_collections_during_tile_retirement >= 0
        assert metrics.python_gc_collected_during_tile_retirement >= 0
        assert metrics.python_gc_uncollectable_during_tile_retirement >= 0
        # Without a charged diagnostic history, exact recreation attribution is unknown.
        assert metrics.tile_recreation_attribution_unknown == 1
    finally:
        recreated.close()


def test_result_eviction_and_unattributed_post_eviction_miss_are_separate() -> None:
    ledger, _actions, _tiles, results, input_lease, output_lease, key, result = _setup()
    held = results.publish(key, result)
    try:
        ledger.evict_query_memos()
        assert results.lookup(key) is None
        metrics = collect_ledger_metrics(ledger)
        assert metrics.completed_result_evictions == 1
        assert metrics.completed_result_evicted_entries >= 1
        assert metrics.completed_result_recomputation_attribution_unknown == 1
    finally:
        held.close()
        output_lease.close()
        input_lease.close()


def test_interface_hits_report_actual_temporal_span_without_semantic_replay() -> None:
    ledger, _tiles, results, source, key, payload = _binding()
    try:
        lookup_causal_interface(results, key)
        publish_causal_interface(results, key, payload)
        lookup_causal_interface(results, key)
        metrics = collect_ledger_metrics(ledger)
        assert metrics.cache_events_by_temporal_span["interface:early_hit:1"] == 1
        assert metrics.cache_events_by_spatial_level["interface:early_hit:0"] == 1
    finally:
        source.close()


def test_cache_histogram_has_a_hard_charged_bucket_bound() -> None:
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    for level in range(MAX_CACHE_EVENT_BUCKETS):
        tiles._cache_metrics.record(
            "tile",
            "publication",
            spatial_level=level,
            temporal_span=None,
        )
    entries = ledger.entries
    tiles._cache_metrics.record(
        "tile",
        "publication",
        spatial_level=MAX_CACHE_EVENT_BUCKETS,
        temporal_span=None,
    )
    assert len(tiles._cache_metrics.buckets) == MAX_CACHE_EVENT_BUCKETS
    assert ledger.entries == entries
    assert ledger.counters["cache_event_histogram_dropped"] == 1
