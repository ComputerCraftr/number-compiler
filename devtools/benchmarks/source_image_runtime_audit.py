"""Audit source-image outputs, replay stability and retained-resource accounting."""

from __future__ import annotations

import json
from time import perf_counter

from devtools.paths import report_directory, repository_root
from devtools.verification.oracles.sequence_arithmetic import (
    collatz_literal as _collatz_scalar,
)
from devtools.verification.oracles.sequence_arithmetic import (
    reverse_add_literal as _reverse_scalar,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

ROOT = repository_root()
INDICES = (16, 32, 64, 128, 256)


def _metric_int(value: object) -> int:
    if type(value) is not int:
        raise AssertionError(("runtime-metric-is-not-an-exact-integer", value))
    return value


def _row(
    term: PoweredCollatzTerm | ReverseAddPoweredTerm,
    expected: int,
    index: int,
) -> dict[str, int | float | str]:
    started = perf_counter()
    low = term.digit(0)
    elapsed = perf_counter() - started
    expected_low = (
        expected % term.base
        if isinstance(term, ReverseAddPoweredTerm)
        else expected & 1
    )
    assert low == expected_low
    assert term.materialize(max_bits=max(1, expected.bit_length())) == expected
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    publication_counter = "source_image_publications"
    projection_counter = "source_image_projection_publications"
    first_publications = metrics.resource_work_counters.get(publication_counter, 0)
    first_projection_publications = metrics.resource_work_counters.get(
        projection_counter, 0
    )
    before_replay = dict(term.resource_ledger.counters)
    assert term.digit(0) == low
    after_replay = term.resource_ledger.counters
    return {
        "index": index,
        "seconds": elapsed,
        "family": behavior.temporal_quotient_family,
        "retained_entries": metrics.resource_ledger_entries,
        "sequential_generation_advances": metrics.sequential_generation_advances,
        "spatial_occurrence_bindings": metrics.spatial_occurrence_bindings,
        "forbidden_future_payloads": metrics.forbidden_future_payloads,
        "representation_boundary_complete": metrics.representation_boundary_complete,
        "runtime_image_matches_oracle": low == expected_low,
        "runtime_image_publications": first_publications,
        "runtime_image_projection_publications": first_projection_publications,
        "replay_publication_delta": after_replay.get(publication_counter, 0)
        - before_replay.get(publication_counter, 0),
        "replay_projection_publication_delta": after_replay.get(projection_counter, 0)
        - before_replay.get(projection_counter, 0),
        "resource_audit_complete": metrics.resource_audit_complete,
        "resource_accounting_mismatch": metrics.resource_accounting_mismatch,
    }


def run() -> dict[str, object]:
    reverse = []
    collatz = []
    for n in INDICES:
        reverse.append(_row(ReverseAddPoweredTerm(196, n), _reverse_scalar(196, n), n))
        collatz.append(
            _row(PoweredCollatzTerm(140137, n), _collatz_scalar(140137, n), n)
        )
    for row in [*reverse, *collatz]:
        assert row["sequential_generation_advances"] == 0
        assert row["spatial_occurrence_bindings"] == 0
        assert row["forbidden_future_payloads"] == 0
        assert row["representation_boundary_complete"] == 1
        assert row["runtime_image_matches_oracle"] is True
        assert _metric_int(row["runtime_image_publications"]) > 0
        assert _metric_int(row["runtime_image_projection_publications"]) > 0
        assert row["replay_publication_delta"] == 0
        assert row["replay_projection_publication_delta"] == 0
        assert row["resource_audit_complete"] == 1
        assert row["resource_accounting_mismatch"] == 0
    return {
        "version": 1,
        "status": "PASS",
        "checkpoint": "runtime-image-output-accounting",
        "reverse_196": reverse,
        "collatz_140137": collatz,
    }


def main() -> int:
    result = run()
    out = (
        report_directory("devtools.benchmarks.source_image_runtime_audit")
        / "source_image_runtime_audit_v1.json"
    )
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
