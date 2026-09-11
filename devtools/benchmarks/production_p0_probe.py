"""Cold scheduler work and repeated public requests, measured independently."""

from __future__ import annotations

import argparse
import json

from devtools.benchmarks.clock_key_growth_probe import measure
from devtools.benchmarks.tile_projection_accounting import projection_accounting
from devtools.checks.test_run_evidence import source_fingerprint
from devtools.paths import repository_root
from number_compiler.api.number_api import (
    NumberCompiler,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
)


def repeated_request(family: str, steps: int) -> dict[str, object]:
    compiler = NumberCompiler()
    seed = 196 if family == "196" else 27
    term = compiler.project_nth(family, steps, seed=seed)
    assert isinstance(
        term.payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    )
    core = term.payload.term
    position = core.maximum_width // 3 if family == "196" else 0
    digit = term.digit(position)
    before_metrics = core._point_index().metrics()
    before = projection_accounting(before_metrics)
    repeat = compiler.project_nth(family, steps, seed=seed)
    assert isinstance(
        repeat.payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    )
    if repeat.payload.term is not core or repeat.digit(position) != digit:
        raise AssertionError("public request lost its exact execution owner")
    after_metrics = core._point_index().metrics()
    if (
        not after_metrics.resource_audit_complete
        or after_metrics.resource_accounting_mismatch
    ):
        raise AssertionError("repeated request resource inventory failed")
    after = projection_accounting(after_metrics)
    delta = {name: after[name] - value for name, value in before.items()}
    if (
        delta["completed_result_entries"]
        or delta["tile_scheduler_leaf_function_applications"]
    ):
        raise AssertionError("warm public request repeated scheduler construction")
    return {
        "family": family,
        "steps": steps,
        "digit": digit,
        "cache": compiler.powered_cache_info(),
        "warm_delta": delta,
        "point_response_hit_delta": (
            after_metrics.resource_work_counters.get("point_response_cache_hits", 0)
            - before_metrics.resource_work_counters.get("point_response_cache_hits", 0)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=("196", "collatz"), required=True)
    parser.add_argument("--mode", choices=("cold", "repeat"), default="cold")
    args = parser.parse_args()
    root = repository_root()
    before = source_fingerprint(root)
    rows = [
        measure(args.family, steps)
        if args.mode == "cold"
        else repeated_request(args.family, steps)
        for steps in (8, 16, 32)
    ]
    after = source_fingerprint(root)
    print(
        json.dumps(
            {
                "source_before": before,
                "source_after": after,
                "source_unchanged": before == after,
                "scope": "bounded execution evidence; first-use logarithmic powering remains unproved",
                "mode": args.mode,
                "rows": rows,
            },
            indent=2,
        )
    )
    if before != after:
        raise AssertionError("source changed during the measurement")


if __name__ == "__main__":
    main()
