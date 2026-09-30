"""Cold source construction plus exact cached/uncached spacetime observations."""

from __future__ import annotations

import argparse
import json
from time import perf_counter

from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
from number_compiler.sequences.antihydra.runtime import run


def measure(
    returns: int, cache_entries: int
) -> tuple[dict[str, object], dict[str, object]]:
    started = perf_counter()
    result = run(returns, max_returns=returns, max_bits=returns + 8)
    constructed = perf_counter()
    output = SpaceTimeProjection(
        result, 2, 2, -1, 1, 3, 2000000, cache_entries=cache_entries
    ).evaluate()
    finished = perf_counter()
    return output, {
        "construction_seconds": constructed - started,
        "projection_seconds": finished - constructed,
        "total_seconds": finished - started,
        "work": dict(result.ledger.counters),
        "peak_nodes": result.ledger.peak_nodes,
        "retained_nodes": result.ledger.nodes,
        "accounting_reconciled": all(
            row.accounting_delta in (0, None) for row in result.ledger.inventory()
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--returns", type=int, default=2048)
    args = parser.parse_args()
    if not 1 <= args.returns <= 4096:
        parser.error("returns must be 1..4096")
    expected, uncached = measure(args.returns, 0)
    actual, cached = measure(args.returns, 32)
    expected.pop("sampled_sweep_classes")
    actual.pop("sampled_sweep_classes")
    if expected != actual:
        raise AssertionError("cached projection changed the typed spacetime image")
    cached_work = cached["work"]
    if type(cached_work) is not dict:
        raise AssertionError("benchmark work counters have the wrong shape")
    discovery = cached_work.get("observer_macro_discovery_steps", 0)
    retained = cached_work.get("observer_retained_support_steps", 0)
    print(
        json.dumps(
            {
                "macro_returns": args.returns,
                "exact_match": True,
                "uncached": uncached,
                "cached": cached,
                "observer_macro_rediscovery_gate_closed": discovery == 0,
                "retained_support_steps": retained,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
