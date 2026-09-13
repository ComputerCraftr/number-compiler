"""Reproducible observer work counts on supplied shared Collatz event actions."""

from __future__ import annotations

import json

from number_compiler.api.cylinder_observation import observe_collatz
from number_compiler.sequences.collatz.power import CollatzEventArena
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers


def run_probe() -> dict[str, object]:
    rows = []
    for level in range(11):
        arena = CollatzEventArena()
        duration = 1 << level
        root = arena.power(arena.event(2), duration)
        before = arena.node_count
        observer = CollatzClockObservers(arena)
        matrix = observer.modular(root, 257)
        expected = (pow(4, duration, 257) - pow(3, duration, 257)) % 257
        if matrix.offset != expected or arena.node_count != before:
            raise AssertionError((level, matrix))
        rows.append(
            {
                "events": duration,
                "reachable_observer_nodes": observer.node_evaluations,
                "skew_compositions": observer.compositions,
                "ring_power_compositions": observer.ring_power_compositions,
                "arena_nodes_added_by_observation": arena.node_count - before,
                "exact_cocycle_materializations": arena.cocycle_materializations,
                "modular_offset": matrix.offset,
            }
        )
    return {
        "scope": "supplied repeated valuation-2 event action; no event discovery claim",
        "modulus": 257,
        "rows": rows,
        "source_derived_rows": [
            {"seed": seed, **observe_collatz(seed, events, kind="modular")}
            for seed in (27, 97, 871)
            for events in (1, 2, 4, 8, 16, 32)
        ],
    }


if __name__ == "__main__":
    print(json.dumps(run_probe(), indent=2))
