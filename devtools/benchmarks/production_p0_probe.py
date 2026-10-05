"""Cold scheduler work and repeated public requests, measured independently."""

from __future__ import annotations

import argparse
import json
from time import perf_counter

from devtools.benchmarks.tile_projection_accounting import projection_accounting
from devtools.git_source import git_source, same_git_revision
from devtools.paths import repository_root
from number_compiler.api.number_api import (
    CommaTermPayload,
    NumberCompiler,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
    ProjectedNumberTerm,
)


def _require_powered_payload(
    payload: object,
) -> PoweredReverseAddTermPayload | PoweredCollatzTermPayload:
    if not isinstance(
        payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    ):
        raise TypeError("expected a powered term payload")
    return payload


def _family_seed_position(family: str, maximum_width: int) -> tuple[int, int]:
    seed = 196 if family == "196" else 27
    position = maximum_width // 3 if family == "196" else 0
    return seed, position


def _project_powered_request(
    compiler: NumberCompiler, family: str, steps: int
) -> tuple[
    ProjectedNumberTerm,
    PoweredReverseAddTermPayload | PoweredCollatzTermPayload,
    int,
    int,
]:
    seed, _ = _family_seed_position(family, 0)
    result = compiler.project_nth(family, steps, seed=seed)
    payload = _require_powered_payload(result.payload)
    core = payload.term
    _, position = _family_seed_position(family, core.maximum_width)
    return result, payload, position, seed


def repeated_request(family: str, steps: int) -> dict[str, object]:
    compiler = NumberCompiler()
    term, payload, position, seed = _project_powered_request(compiler, family, steps)
    core = payload.term
    digit = term.digit(position)
    before_metrics = core.metrics()
    before = projection_accounting(before_metrics)
    repeat = compiler.project_nth(family, steps, seed=seed)
    repeat_payload = _require_powered_payload(repeat.payload)
    if repeat_payload.term is not core or repeat.digit(position) != digit:
        raise AssertionError("public request lost its exact execution owner")
    after_metrics = core.metrics()
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


def cold_request(family: str, steps: int) -> dict[str, object]:
    compiler = NumberCompiler()
    result, payload, position, _seed = _project_powered_request(compiler, family, steps)
    core = payload.term
    digit = result.digit(position)
    metrics = core.metrics()
    return {
        "family": family,
        "steps": steps,
        "digit": digit,
        "cache": compiler.powered_cache_info(),
        "cold": projection_accounting(metrics),
    }


def comma_arithmetic_requests(
    mode: str,
    trials: int,
    indices: tuple[int, ...],
    *,
    certified: bool,
) -> list[dict[str, object]]:
    """Measure construction separately from certificate admission and rendering."""
    rows: list[dict[str, object]] = []
    for index in indices:
        retained = NumberCompiler()
        if mode == "repeat":
            warm = retained.project_nth("a367620", index)
            assert isinstance(warm.payload, CommaTermPayload)
            if certified:
                warm.materialize(max_bits=1_000_000)
            else:
                warm.payload.term.materialize()
        for trial in range(trials):
            if certified and mode == "cold":
                NumberCompiler.clear_shared_cache()
            compiler = (
                retained
                if mode == "repeat"
                else NumberCompiler(
                    max_cached_terms=0 if mode == "bypass" else 8,
                    shared_cache=mode != "bypass",
                )
            )
            start = perf_counter()
            projected = compiler.project_nth("a367620", index)
            assert isinstance(projected.payload, CommaTermPayload)
            term = projected.payload.term
            descriptor_end = perf_counter()
            before = dict(term.ledger.counters)
            if certified:
                projected.payload.require_certified()
            admission_end = perf_counter()
            value = term.materialize()
            construction_end = perf_counter()
            clock = term.clock()
            width = term.width()
            observation_end = perf_counter()
            digits = "".join(
                str(digit) for digit in reversed(tuple(term.iter_digits()))
            )
            end = perf_counter()
            assert int(digits) == value and len(digits) == width
            rows.append(
                {
                    "index": index,
                    "trial": trial,
                    "mode": mode,
                    "index_unit": "oeis_index",
                    "value": value,
                    "descriptor_seconds": descriptor_end - start,
                    "certificate_seconds": admission_end - descriptor_end,
                    "construction_seconds": construction_end - admission_end,
                    "observation_seconds": observation_end - construction_end,
                    "render_seconds": end - observation_end,
                    "clock": clock,
                    "work": dict(term.ledger.counters),
                    "incremental_work": {
                        key: count - before.get(key, 0)
                        for key, count in term.ledger.counters.items()
                    },
                    "entries": term.ledger.entries,
                    "nodes": term.ledger.nodes,
                    "owner_cache": compiler.powered_cache_info(),
                }
            )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--family", choices=("196", "collatz", "a367620"), required=True
    )
    parser.add_argument("--mode", choices=("cold", "repeat", "bypass"), default="cold")
    parser.add_argument("--arithmetic-only", action="store_true")
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--indices", nargs="+", type=int)
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("--trials must be positive")
    if args.family != "a367620" and (args.arithmetic_only or args.indices):
        parser.error("--arithmetic-only and --indices apply only to a367620")
    last_index = 412987859 if args.arithmetic_only else 412987860
    indices = tuple(
        args.indices or (16, 32, 64, 128, 256, 512, 1024, 20000, last_index)
    )
    if any(index < 1 for index in indices):
        parser.error("comma indices must be positive")
    if args.family != "a367620" and args.mode == "bypass":
        parser.error("--mode bypass is currently available for a367620 only")
    root = repository_root()
    before = git_source(root)
    rows = (
        comma_arithmetic_requests(
            args.mode, args.trials, indices, certified=not args.arithmetic_only
        )
        if args.family == "a367620"
        else [
            cold_request(args.family, steps)
            if args.mode == "cold"
            else repeated_request(args.family, steps)
            for steps in (8, 16, 32)
        ]
    )
    after = git_source(root)
    revision_unchanged = same_git_revision(before, after)
    print(
        json.dumps(
            {
                "git_source_before": before.as_dict(),
                "git_source_after": after.as_dict(),
                "git_revision_unchanged": revision_unchanged,
                "scope": (
                    (
                        "finite arithmetic only; certificate admission excluded; "
                        if args.arithmetic_only
                        else "runtime-certified prefix API; "
                    )
                    + "warm interpreter; cold clears shared cache, repeat retains owner; "
                    + "bypass disables process/API reuse, not within-request memoization"
                    if args.family == "a367620"
                    else "bounded execution evidence; first-use logarithmic powering remains unproved"
                ),
                "mode": args.mode,
                "rows": rows,
            },
            indent=2,
        )
    )
    if not revision_unchanged:
        raise AssertionError("Git revision changed during the measurement")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
