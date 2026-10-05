"""Deterministic finite audit for the normalized inverse-three clock."""

from __future__ import annotations

import json

from number_compiler.sequences.collatz.inverse_three_clock import (
    ClockedTangentArena,
    InverseThreeClock,
    radix64_cylinder_views,
)


def build_report() -> dict[str, object]:
    arena = ClockedTangentArena()
    skeletons: set[tuple[object, ...]] = set()
    curvature_packets: set[tuple[int, ...]] = set()
    contexts = 0
    for phase in range(16):
        clock = InverseThreeClock(6, phase)
        for digit in range(64):
            contexts += 1
            skeletons.add(arena.compile(clock, digit).skeleton.canonical_key)
            curvature_packets.add(radix64_cylinder_views(clock, digit).curvature)
    lifts = {}
    for precision in range(6, 19):
        coefficients = {
            InverseThreeClock(precision, phase).lift_coefficient
            for phase in range(min(16, 1 << (precision - 2)))
        }
        lifts[str(precision)] = sorted(coefficients)
    growth = []
    for extent in (16, 32, 64, 128, 256, 512, 1024):
        clock_keys = {
            InverseThreeClock(6, phase).canonical_key for phase in range(extent)
        }
        local_arena = ClockedTangentArena()
        for phase in range(extent):
            clock = InverseThreeClock(6, phase)
            for source_digit in range(64):
                local_arena.compile(clock, source_digit)
        growth.append(
            {
                "extent": extent,
                "raw_phase_occurrences": extent,
                "canonical_clock_keys": len(clock_keys),
                "consumer_requests": local_arena.requests,
                "retained_skeletons": local_arena.retained_skeletons,
                "skeleton_cache_hits": local_arena.cache_hits,
            }
        )
    return {
        "low_contexts": contexts,
        "tangent_skeletons": len(skeletons),
        "curvature_packets": len(curvature_packets),
        "normalized_hasse_jet": [0, 1],
        "skeleton_cache_hits": arena.cache_hits,
        "mismatch_depths": list(range(6)),
        "match_consumed_bits": 6,
        "lift_coefficients_by_precision": lifts,
        "finite_window_is_successor_complete": False,
        "exact_spatial_tangent_payload_retained": True,
        "phase_consumer_growth": growth,
    }


def main() -> None:
    print(json.dumps(build_report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
