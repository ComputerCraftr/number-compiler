import json
from pathlib import Path

from devtools.benchmarks.collatz_temporal_power_probe import _scalar
from devtools.benchmarks.reverse_temporal_power_probe import _scalar_digit
from devtools.checks.test_run_evidence import source_fingerprint

root = Path.cwd()
base = root / "results/current/production-p0-2026-09-11"
out = base / "release-audit"
manifest = json.loads((out / "manifest.json").read_text())
assert source_fingerprint(root) == manifest["source_fingerprint"]
rows = []
for family in ("196", "collatz"):
    for horizon in (32, 64):
        result = json.loads((out / f"cli-{family}-{horizon}.json").read_text())
        expected = (
            sum(
                _scalar_digit(horizon, position) * 10**position
                for position in range(3 + horizon)
            )
            if family == "196"
            else _scalar(27, horizon)
        )
        assert int(result["value"]) == expected
        metrics = result["execution_metrics"]
        assert metrics["resource_audit_complete"]
        assert metrics["resource_accounting_mismatch"] == 0
        counters = metrics["resource_work_counters"]
        row = {
            "family": family,
            "horizon": horizon,
            "exact_oracle_match": True,
            "value": result["value"],
            **{
                key: metrics[key]
                for key in (
                    "completed_result_entries",
                    "completed_result_evaluations",
                    "completed_result_early_hits",
                    "resource_ledger_entries",
                    "resource_ledger_nodes",
                )
            },
            **{
                key: counters.get(key, 0)
                for key in (
                    "primitive_behavior_refinement_observation_checks",
                    "primitive_behavior_refinement_successor_checks",
                    "tile_causal_primitive_emits",
                    "reverse_threshold_summary_known_missing_probe_elisions",
                    "collatz_physical_event_source_reads_elided",
                )
            },
        }
        old_path = base / "final-verified" / f"cli-{family}-{horizon}.json"
        if old_path.exists():
            old = json.loads(old_path.read_text())
            assert result["value"] == old["value"]
            row["prior_observation_checks"] = old["execution_metrics"][
                "resource_work_counters"
            ]["primitive_behavior_refinement_observation_checks"]
        rows.append(row)
warm_rows = []
for family in ("196", "collatz"):
    report = json.loads((out / f"{family}-repeat.json").read_text())
    assert report["source_unchanged"]
    for row in report["rows"]:
        assert row["cache"]["hits"] == 1
        assert row["point_response_hit_delta"] == 1
        assert all(value == 0 for value in row["warm_delta"].values())
        warm_rows.append(
            {
                "family": family,
                "horizon": row["steps"],
                "api_hits": 1,
                "new_scheduler_work": 0,
            }
        )
assert source_fingerprint(root) == manifest["source_fingerprint"]
print(
    json.dumps(
        {
            "source_fingerprint": manifest["source_fingerprint"],
            "release_ready": False,
            "passed_tests": sum(row.get("passed_tests", 0) for row in manifest["jobs"]),
            "theories": len(manifest["theories"]),
            "cli_rows": rows,
            "warm_public_requests": warm_rows,
        },
        indent=2,
    )
)
