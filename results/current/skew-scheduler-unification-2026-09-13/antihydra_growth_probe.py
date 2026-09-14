"""Bounded cold, same-run repeat and bypass observations; no powering claim."""

from __future__ import annotations

import json
from time import perf_counter
from typing import Any

from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
from number_compiler.sequences.antihydra.runtime import run


def semantic(packet: dict[str, object]) -> dict[str, object]:
    return {name: value for name, value in packet.items() if name != "sampled_sweep_classes"}


def measure(horizon: int, trial: int) -> dict[str, Any]:
    started = perf_counter()
    source = run(horizon, max_returns=horizon, max_bits=horizon + 8)
    constructed = perf_counter()
    projection = SpaceTimeProjection(source, 2, 2, -1, 1, 3, 2_000_000)
    cold = projection.evaluate()
    observed = perf_counter()
    cold_counters = dict(source.ledger.counters)
    cold_nodes = source.ledger.nodes
    repeated = projection.evaluate()
    warmed = perf_counter()
    warm_counters = dict(source.ledger.counters)
    warm_nodes = source.ledger.nodes
    if semantic(cold) != semantic(repeated):
        raise AssertionError("same-run projection changed its semantic lanes")
    required = (
        "source_image_primitive_applications",
        "spacetime_projection_fragment_leaf_returns",
        "spacetime_projection_fragment_hits",
    )
    if any(name not in warm_counters for name in required):
        raise AssertionError("required observation instrumentation is missing")
    if cold_counters["spacetime_projection_fragment_leaf_returns"] != horizon:
        raise AssertionError("cold projection did not charge every visited return")
    warm_delta = {
        name: count - cold_counters.get(name, 0)
        for name, count in warm_counters.items()
    }
    if warm_delta["source_image_primitive_applications"] != 0:
        raise AssertionError("same-run repeat reconstructed source fragments")
    if warm_delta["spacetime_projection_fragment_leaf_returns"] != 0:
        raise AssertionError("same-run repeat replayed the retained leaf support")
    bypass_started = perf_counter()
    bypass_source = run(horizon, max_returns=horizon, max_bits=horizon + 8)
    bypass_constructed = perf_counter()
    bypass = SpaceTimeProjection(
        bypass_source, 2, 2, -1, 1, 3, 2_000_000, cache_entries=0
    ).evaluate()
    bypass_finished = perf_counter()
    if semantic(cold) != semantic(bypass):
        raise AssertionError("bypassing retained fragments changed the semantic lanes")
    return {
        "horizon": horizon,
        "trial": trial,
        "construction_seconds": constructed - started,
        "cold_observation_seconds": observed - constructed,
        "same_run_repeat_seconds": warmed - observed,
        "bypass_construction_seconds": bypass_constructed - bypass_started,
        "bypass_observation_seconds": bypass_finished - bypass_constructed,
        "cold_counters": cold_counters,
        "same_run_incremental_counters": warm_delta,
        "bypass_counters": dict(bypass_source.ledger.counters),
        "cold_retained_nodes": cold_nodes,
        "repeat_retained_nodes": warm_nodes,
        "peak_nodes_since_construction": source.ledger.peak_nodes,
        "bypass_retained_nodes": bypass_source.ledger.nodes,
        "bypass_peak_nodes": bypass_source.ledger.peak_nodes,
        "accounting_reconciled": all(
            row.accounting_delta in (0, None)
            for ledger in (source.ledger, bypass_source.ledger)
            for row in ledger.inventory()
        ),
    }


def main() -> None:
    rows = [measure(horizon, trial) for horizon in (16, 32, 64, 128, 256, 512, 1024)
            for trial in range(1, 6)]
    if any(not row["accounting_reconciled"] for row in rows):
        raise AssertionError("observation retention is not reconciled")
    print(json.dumps({
        "scope": "API observation controls; same-run reuse is not new-query CLI reuse",
        "horizons": [16, 32, 64, 128, 256, 512, 1024],
        "trials_per_horizon": 5,
        "samples": rows,
        "semantic_match": True,
        "arbitrary_powered_construction_claim": False,
    }))


if __name__ == "__main__":
    main()
