#!/usr/bin/env python3
"""Freeze the bounded T^2/C^4 checkpoint before higher-rung HashLife closure."""

from __future__ import annotations

import json
from time import perf_counter
from typing import TYPE_CHECKING

from devtools.paths import repository_root
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


ROOT = repository_root()
INDICES = (16, 32, 64, 128, 256)


def _reverse_scalar(steps: int) -> int:
    value = 196
    for _ in range(steps):
        text = str(value)
        value += int(text[::-1])
    return value


def _collatz_scalar(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = 3 * value + 1 if value & 1 else value // 2
    return value


def _row(
    term: PoweredCollatzTerm | ReverseAddPoweredTerm,
    expected: int,
    index: int,
) -> dict[str, int | float | str]:
    started = perf_counter()
    low = term.digit(0)
    elapsed = perf_counter() - started
    assert low == expected % term.base if hasattr(term, "base") else low == expected & 1
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    return {
        "index": index,
        "seconds": elapsed,
        "family": behavior.temporal_quotient_family,
        "machine_applications": metrics.bounded_application_action_applications,
        "machine_symbol_visits": metrics.resource_work_counters.get(
            "family_bisimulation_symbol_visits", 0
        ),
        "retained_entries": metrics.resource_ledger_entries,
        "microblock_entries": metrics.exact_microblock_entries,
        "transient_payload_peak_bytes": metrics.resource_work_counters.get(
            "family_bisimulation_transient_payload_peak_bytes", 0
        ),
        "sequential_generation_advances": metrics.sequential_generation_advances,
        "spatial_occurrence_bindings": metrics.spatial_occurrence_bindings,
        "forbidden_future_payloads": metrics.forbidden_future_payloads,
        "representation_boundary_complete": metrics.representation_boundary_complete,
        "cutover_complete": behavior.bounded_temporal_runtime_cutover_complete,
    }


def run() -> dict[str, object]:
    reverse = []
    collatz = []
    for n in INDICES:
        reverse.append(_row(ReverseAddPoweredTerm(196, n), _reverse_scalar(n), n))
        collatz.append(
            _row(PoweredCollatzTerm(140137, n), _collatz_scalar(140137, n), n)
        )
    assert [row["machine_applications"] for row in reverse] == [9, 17, 33, 65, 129]
    assert [row["machine_applications"] for row in collatz] == [4, 8, 16, 32, 64]
    for row in [*reverse, *collatz]:
        assert row["sequential_generation_advances"] == 0
        assert row["spatial_occurrence_bindings"] == 0
        assert row["forbidden_future_payloads"] == 0
        assert row["representation_boundary_complete"] == 1
        assert row["cutover_complete"] == 1
        assert int(row["transient_payload_peak_bytes"]) <= 256
    return {
        "version": 1,
        "status": "PASS",
        "checkpoint": "linear-temporal-bisimulation-t2-c4",
        "logarithmic_temporal_closure_proved": False,
        "note": "Machine-rung count is linear; full symbol visits are not claimed logarithmic or linear in N.",
        "reverse_196": reverse,
        "collatz_140137": collatz,
    }


def main() -> int:
    result = run()
    out = ROOT / "results" / "linear_bisimulation_checkpoint_v1.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
