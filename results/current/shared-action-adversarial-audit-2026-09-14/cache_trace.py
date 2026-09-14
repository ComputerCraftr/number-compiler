"""Bounded actual prime CLI keys and Antihydra cache eviction controls."""

from __future__ import annotations

from collections import Counter
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from unittest.mock import patch

from number_compiler.api import cli
from number_compiler.api.number_api import NumberCompiler
from number_compiler.resources.process_cache import CacheLease
from number_compiler.sequences.antihydra.runtime import CylinderEngine


def prime_traces() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    get, put = CacheLease.get, CacheLease.put
    counts: Counter[str] = Counter()

    def visit(key, mode):
        if type(key) is tuple and len(key) == 3 and key[0] == "phi":
            counts[mode] += 1
            counts[mode + "_prefix_elements"] += len(key[1])
            counts["maximum_prefix_depth"] = max(counts["maximum_prefix_depth"], len(key[1]))

    def traced_get(self, key, *args, **kwargs):
        visit(key, "phi_get")
        return get(self, key, *args, **kwargs)

    def traced_put(self, key, value, *args, **kwargs):
        visit(key, "phi_put")
        return put(self, key, value, *args, **kwargs)

    NumberCompiler().clear_shared_cache()
    with patch.object(CacheLease, "get", traced_get), patch.object(CacheLease, "put", traced_put):
        for index in (1000, 1000, 5000, 5000):
            counts.clear()
            out, err = io.StringIO(), io.StringIO()
            arguments = ["prime", "--nth", str(index), "--info", "metrics", "--format", "json"]
            with redirect_stdout(out), redirect_stderr(err):
                code = cli.main(arguments)
            rows.append({
                "arguments": arguments, "exit_code": code, "stderr": err.getvalue(),
                "shared_phi_key_visits": dict(counts),
                "packet": json.loads(out.getvalue()) if out.getvalue() else None,
            })
    return rows


def eviction_trace() -> dict[str, object]:
    engine = CylinderEngine(max_cache_entries=64)
    engine.cylinder(0, 8)
    engine.arithmetic_cylinder(0, 8)
    evictions: list[dict[str, object]] = []
    for residue in range(1, 41):
        before = engine.ledger.counters.get("cache_evictions", 0)
        sizes = [len(engine.memo), len(engine.arithmetic_memo)]
        engine.arithmetic_cylinder(residue, 8)
        after = engine.ledger.counters.get("cache_evictions", 0)
        if after != before:
            evictions.append({
                "residue": residue, "prior_memo_sizes": sizes,
                "new_memo_sizes": [len(engine.memo), len(engine.arithmetic_memo)],
                "evicted_entries": after-before,
            })
    before = dict(engine.ledger.counters)
    engine.arithmetic_cylinder(0, 8)
    engine.cylinder(0, 8)
    return {
        "scope": "bounded engine control; not a measured default-CLI cache-saturation workload",
        "capacity": 64, "evictions": evictions,
        "repeat_incremental_counters": {
            key: value-before.get(key, 0) for key, value in engine.ledger.counters.items()
        },
    }


if __name__ == "__main__":
    print(json.dumps({"prime": prime_traces(), "antihydra": eviction_trace()}))
