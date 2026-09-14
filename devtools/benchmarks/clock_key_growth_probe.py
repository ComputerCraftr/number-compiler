"""Measure real warm reuse and reject lossy occurrence-key projections.

Clock research actions are not installed as production result-cache keys.
These measurements deliberately keep observed output aliases separate from
proved, context-independent action equivalence.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterable

from devtools.benchmarks.collatz_temporal_power_probe import _scalar
from devtools.benchmarks.reverse_temporal_power_probe import _scalar_digit
from devtools.benchmarks.tile_projection_accounting import (
    projection_accounting,
    retained_result_profile,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    NormalizedRegionKey,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _partition(
    entries: Iterable[tuple[tuple[object, ...], CompletedResult]],
) -> dict[str, object]:
    """Count observed conflicts; zero conflicts is not a universal proof."""
    fibers: dict[tuple[object, ...], set[CompletedResult]] = {}
    count = 0
    for key, value in entries:
        count += 1
        fibers.setdefault(key, set()).add(value)
    conflicts = [outputs for outputs in fibers.values() if len(outputs) > 1]
    return {
        "entries": count,
        "projected_keys": len(fibers),
        "potential_key_aliases": count - len(fibers),
        "conflicted_fibers": len(conflicts),
        "max_distinct_outputs": max(map(len, fibers.values()), default=0),
        "promotion_certified": False,
    }


def occurrence_key_ablations(
    arena: CompletedResultArena,
    *,
    max_entries: int = 20_000,
) -> dict[str, object]:
    """Inspect retained IDs only; never discover an output to create a key."""
    entries: list[tuple[PoweredResultKey, CompletedResult]] = []
    regions: Counter[int] = Counter()
    for key, value in arena._memo.items():
        if type(key) is NormalizedRegionKey:
            regions[key.view.relative_origin] += 1
        if type(key) is PoweredResultKey and type(value) is CompletedResult:
            if len(entries) >= max_entries:
                raise ValueError("occurrence-key ablation exceeds entry budget")
            entries.append((key, value))
    fields = ("action", "input", "ports", "wiring", "boundaries", "fusion", "region")
    projections: dict[str, tuple[str, ...]] = {
        "full_key": fields,
        "omit_ports": tuple(name for name in fields if name != "ports"),
        "omit_boundaries": tuple(name for name in fields if name != "boundaries"),
        "omit_input": tuple(name for name in fields if name != "input"),
        "finite_contract_only": ("action", "ports", "wiring", "fusion"),
    }
    return {
        "projections": {
            name: _partition(
                (tuple(getattr(key, field) for field in selected), value)
                for key, value in entries
            )
            for name, selected in projections.items()
        },
        "wiring_phases": dict(
            sorted(Counter(key.wiring.phase for key, _ in entries).items())
        ),
        "region_normalization_origins": dict(sorted(regions.items())),
        "production_clock_action_interner_present": False,
    }


def measure(family: str, steps: int) -> dict[str, object]:
    """Observe a cold point and the identical warm request on the public term."""
    term: ReverseAddPoweredTerm | PoweredCollatzTerm
    if family == "196":
        term = ReverseAddPoweredTerm(196, steps, base=10)
        position = term.maximum_width // 3
        expected = _scalar_digit(steps, position)
    elif family == "collatz":
        term = PoweredCollatzTerm(27, steps)
        position = 0
        expected = _scalar(27, steps) & 1
    else:
        raise ValueError("clock probe requires 196 or physical Collatz")
    assert term.digit(position) == expected
    index = term._point_index()
    cold_metrics = index.metrics()
    cold = projection_accounting(cold_metrics)
    microblock_counters = (
        "microblock_requests",
        "microblock_hits",
        "microblock_publications",
        "point_response_requests",
        "point_response_cache_hits",
        "point_response_evaluations",
    )
    cold.update(
        {
            name: cold_metrics.resource_work_counters.get(name, 0)
            for name in microblock_counters
        }
    )
    application = index._lazy_application
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    if type(application) is not LazyProjection:
        raise AssertionError("Collatz clock probe requires the tile projection")
    profile = retained_result_profile(application.scheduler.results)
    ablations = occurrence_key_ablations(application.scheduler.results)
    assert term.digit(position) == expected
    warm_metrics = index.metrics()
    warm = projection_accounting(warm_metrics)
    warm.update(
        {
            name: warm_metrics.resource_work_counters.get(name, 0)
            for name in microblock_counters
        }
    )
    if (
        not warm_metrics.resource_audit_complete
        or warm_metrics.resource_accounting_mismatch
    ):
        raise AssertionError("warm projection resource inventory failed")
    return {
        "family": family,
        "steps": steps,
        "position": position,
        "digit": expected,
        "cold": cold,
        "warm_delta": {name: warm[name] - value for name, value in cold.items()},
        **profile,
        "key_ablations": ablations,
    }


def report() -> dict[str, object]:
    return {
        "scope": "Observed bound results; no new production equality is certified",
        "rows": [
            measure(family, steps)
            for family in ("196", "collatz")
            for steps in (8, 16, 32)
        ],
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
