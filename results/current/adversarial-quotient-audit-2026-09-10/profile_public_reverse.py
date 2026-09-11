"""Read-only cold query profile; profiled time is not a release timing."""

import cProfile
import json
import pstats
import sys
from dataclasses import asdict
from pathlib import Path
from time import perf_counter

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

steps = int(sys.argv[1])
prefix = Path(sys.argv[2])
term = ReverseAddPoweredTerm(196, steps, max_cache_entries=180000)
profiler = cProfile.Profile()
started = perf_counter()
profiler.enable()
value = term.digit(0)
profiler.disable()
query_seconds = perf_counter() - started
profiler.dump_stats(str(prefix) + ".pstats")
started = perf_counter()
metrics = asdict(term.metrics())
metric_seconds = perf_counter() - started
metrics.pop("resource_inventory", None)
expected = 196
for _ in range(steps):
    expected += int(str(expected)[::-1])
assert value == expected % 10
stats = pstats.Stats(profiler)
rows = [
    {
        "file": key[0],
        "line": key[1],
        "function": key[2],
        "primitive_calls": record[0],
        "calls": record[1],
        "self_seconds": record[2],
        "cumulative_seconds": record[3],
    }
    for key, record in getattr(stats, "stats").items()
]
report = {
    "steps": steps,
    "value": value,
    "profiled": True,
    "query_seconds": query_seconds,
    "metrics_seconds": metric_seconds,
    "total_calls": getattr(stats, "total_calls"),
    "top_self": sorted(rows, key=lambda r: r["self_seconds"], reverse=True)[:30],
    "top_cumulative": sorted(rows, key=lambda r: r["cumulative_seconds"], reverse=True)[
        :30
    ],
    "counters": dict(term._ledger.counters),
}
print(json.dumps(report, indent=2))
