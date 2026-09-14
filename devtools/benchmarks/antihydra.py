"""Cold/warm Python Antihydra roofs against the canonical one-return action."""

from __future__ import annotations

import argparse
import json
from time import perf_counter

from number_compiler.sequences.antihydra.blocks import kernel
from number_compiler.sequences.antihydra.runtime import CylinderEngine


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--returns", type=int, default=32768)
    args = parser.parse_args()
    count = args.returns
    if not 1 <= count <= 200000:
        parser.error("returns must be 1..200000")
    engine = CylinderEngine()
    start = perf_counter()
    cold = engine.execute(count, max_returns=count, max_bits=count+8)
    cold_seconds = perf_counter()-start
    cold_counters = dict(engine.ledger.counters)
    start = perf_counter()
    warm = engine.execute(count, max_returns=count, max_bits=count+8)
    warm_seconds = perf_counter()-start
    atoms = kernel(0, 1), kernel(1, 1)
    h, a, left, right = 8, 0, 5, 6
    start = perf_counter()
    for _ in range(count):
        h, a, dl, dr = atoms[h & 1].apply(h, a)
        left += dl
        right += dr
    scalar_seconds = perf_counter()-start
    expected = h, a, left, right
    if any((result.h, result.balance, result.left, result.right) != expected
           for result in (cold, warm)):
        raise AssertionError("powered and scalar physical actions disagree")
    print(json.dumps({
        "returns": count, "cold_seconds": cold_seconds, "warm_seconds": warm_seconds,
        "scalar_physical_seconds": scalar_seconds,
        "cold_speedup": scalar_seconds/cold_seconds,
        "cold_work": cold_counters,
        "warm_work": {key: value-cold_counters.get(key, 0)
                      for key, value in engine.ledger.counters.items()},
        "h_bits": h.bit_length(), "physical_ticks_bits": (left+right).bit_length(),
        "peak_nodes": engine.ledger.peak_nodes, "retained_nodes": engine.ledger.nodes,
        "exact_match": True, "nonhalting_certified": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
