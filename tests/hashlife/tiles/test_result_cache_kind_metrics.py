"""GC metrics distinguish powered results from behavior and region reuse."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.tiles.tile_behavior_memo import (
    lookup_behavior_classification,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_region_memo import (
    lookup_normalized_region,
    normalize_cached_region,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    NormalizedRegionKey,
    PoweredResultKey,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.result_cache_kinds import result_cache_kind
from tests.support.tile_kernel import make_tile_from_symbols, powered_runtime


def test_eviction_and_unknown_recreation_are_attributed_by_cache_kind() -> None:
    ledger, tiles, adapter, primitive, scheduler, action, blank = powered_runtime(
        BaseBlockEffect(3), 4
    )
    engine = CausalTileEngine(scheduler)
    with make_tile_from_symbols(tiles, adapter, primitive, (blank,) * 4) as source:
        left, right = engine.initial_state(action, 0), engine.initial_state(action, 1)
        ports = adapter.initial_ports(action)
        with scheduler.complete(
            action,
            source.tile,
            ports,
            adapter.wiring(action),
        ):
            assert (
                quiescent_boundary(
                    engine,
                    action,
                    0,
                    BoundaryTileView(source.tile, 0, 4),
                    left,
                    right,
                )
                is not None
            )
            raw = BoundaryTileView(source.tile, 7, 2, 0, 1)
            _normalized, region_lease = normalize_cached_region(scheduler.results, raw)
            try:
                keys = tuple(scheduler.results.audit_snapshot().memo)
                result_key = next(
                    key
                    for key in keys
                    if type(key) is PoweredResultKey
                    and key.action == action
                    and key.input == source.tile
                )
                behavior_key = next(
                    key for key in keys if type(key) is BehaviorBindingKey
                )
                region_key = next(
                    key for key in keys if type(key) is NormalizedRegionKey
                )
                assert any(type(key) is PoweredResultKey for key in keys)
                expected = {
                    kind: 0
                    for kind in ("result", "interface", "behavior", "region", "spatial")
                }
                for key in keys:
                    expected[result_cache_kind(key)] += 1
                scheduler.results.clear()
                for kind, count in expected.items():
                    assert (
                        ledger.counters.get(
                            f"result_cache_{kind}_evicted_entries",
                            0,
                        )
                        == count
                    )
                assert ledger.counters[
                    "result_cache_kind_classification_visits"
                ] == len(keys)
                assert scheduler.results.lookup(result_key) is None
                assert (
                    lookup_behavior_classification(
                        scheduler.results,
                        behavior_key,
                    )
                    is None
                )
                assert lookup_normalized_region(scheduler.results, region_key) is None
                for kind in ("result", "behavior", "region"):
                    assert (
                        ledger.counters[
                            f"result_cache_{kind}_post_eviction_misses_attribution_unknown"
                        ]
                        == 1
                    )
                before_report = ledger.snapshot()
                report = collect_ledger_metrics(ledger)
                assert report.result_cache_result_evicted_entries == expected["result"]
                assert (
                    report.result_cache_behavior_evicted_entries == expected["behavior"]
                )
                assert report.result_cache_region_evicted_entries == expected["region"]
                assert ledger.snapshot() == before_report
            finally:
                region_lease.close()


def test_retirement_removals_keep_behavior_and_region_distinct() -> None:
    ledger, tiles, adapter, primitive, scheduler, action, blank = powered_runtime(
        BaseBlockEffect(3), 4
    )
    engine = CausalTileEngine(scheduler)
    source = make_tile_from_symbols(tiles, adapter, primitive, (blank,) * 4)
    left, right = engine.initial_state(action, 0), engine.initial_state(action, 1)
    assert (
        quiescent_boundary(
            engine,
            action,
            0,
            BoundaryTileView(source.tile, 0, 4),
            left,
            right,
        )
        is not None
    )
    source.close()
    assert ledger.counters["result_cache_behavior_retirement_removals"] == 1

    with make_tile_from_symbols(
        tiles, adapter, primitive, (blank, 0, 1, blank)
    ) as backing:
        _view, lease = normalize_cached_region(
            scheduler.results,
            BoundaryTileView(backing.tile, 0, 2, 0, 1),
        )
        lease.close()
    assert ledger.counters["result_cache_region_retirement_removals"] == 1
