from pathlib import Path
import json
import sys
from collections import Counter

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/performance-agent-closure-2026-09-13")
frozen = json.loads((out / "source-freeze.json").read_text())
assert source_fingerprint(Path.cwd()) == frozen["source_fingerprint"]
growth = json.loads((out / "growth-manifest/report.json").read_text())
guards = [
    json.loads(p.read_text())
    for p in sorted((out / "growth-manifest").glob("*.guard.json"))
]
counts = dict(Counter(g["outcome"] for g in guards))
prime = []
for name in ("cold-current", "cold-historical"):
    d = json.loads((out / (name + ".log")).read_text())
    for row in d["rows"]:
        b, c = row["baseline_median_seconds"], row["candidate_median_seconds"]
        prime.append(
            {
                "measurement": name,
                "case": row["case"],
                "baseline_ms": 1000 * b,
                "candidate_ms": 1000 * c,
                "passes": c <= b + max(0.1 * b, 0.001),
            }
        )
for name in ("warm-current", "warm-historical"):
    d = json.loads((out / (name + ".log")).read_text())
    for case, row in d["comparisons"].items():
        prime.append(
            {
                "measurement": name,
                "case": case,
                "baseline_ms": 1000 * row["baseline_median_seconds"],
                "candidate_ms": 1000 * row["candidate_median_seconds"],
                "passes": row["passes"],
            }
        )
summary = {
    "release_status": "BLOCKED",
    "source_fingerprint": frozen["source_fingerprint"],
    "wheel_sha256": frozen["wheel_sha256"],
    "unit": {"passed": 5127, "failed": 4, "deselected": 1277},
    "explicit_p0": {"passed": 7, "failed": 15},
    "growth": {
        "attempted_trials": len(guards),
        "guard_outcomes": counts,
        "status": growth["status"],
        "collection_complete": growth["collection_complete"],
        "release_manifest_complete": growth["release_manifest_complete"],
    },
    "prime_latency": prime,
    "independent_release_signoff": False,
}
(out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
table = "\n".join(
    f"| {r['measurement']} / {r['case']} | {r['baseline_ms']:.3f} | {r['candidate_ms']:.3f} | {'PASS' if r['passes'] else 'FAIL'} |"
    for r in prime
)
text = f"""# Frozen performance validation — September 13

**Release status: BLOCKED.** The implementation and remaining construction/proof
obligations are described in the [coordinator report](../../../docs/performance-agent-closure-2026-09-13.md).

Source fingerprint: `{frozen["source_fingerprint"]}`.
Wheel SHA-256: `{frozen["wheel_sha256"]}`.
[Source inventory](source-freeze.json), [installed wheel/source comparison](wheel-source-match.json),
[independent audit](independent-review.json), [machine-readable summary](summary.json).
All 501 packaged Python files match the frozen tree. No release sign-off is granted.

## Validation result

- [Full unit suite](full-unit.log): **5,127 passed, four unchanged failures, 1,277 deselected**;
  [guard](full-unit.guard.json): 268.49 seconds, 696,959,960 sampled peak bytes, within 300 seconds/1 GiB.
- [Explicit unchanged P0 selection](explicit-p0.log): **15 failed, seven passed**.
- [Installed wheel](installed-wheel.log): family-first syntax, checked M11 factor,
  output, budget and migration contracts pass.
- [Authored-source typing](authored-mypy.log), [Ruff](authored-ruff.log), and
  [structural/ownership policy](policy.log) pass.
- Whole-directory [mypy](whole-tree-mypy.log) and [Ruff](whole-tree-ruff.log) are
  blocked by older result-artifact module duplication and formatting, separately
  from the passing `src tests devtools` checks. No exclusion or assertion was weakened.
- [Prime Isabelle](isabelle-prime.log), [reverse/add](isabelle-Reverse_Residuals.log),
  [étale](isabelle-Etale_Primary_Carry.log), and [Antihydra](isabelle-Antihydra.log)
  build within their 35-second/4-GiB guards. The first [temporal build](isabelle-Temporal_Clock_Jumps.log)
  timed out while constructing its reverse/add parent heap. Subsequent explicitly
  guarded heap/build attempts, if present, are recorded separately.

## Paired prime latency

Five samples per condition; units are milliseconds. Acceptance is at most the
baseline median plus `max(10%, 1 ms)`. Warm probes also execute cache-bypassed
candidate controls and compare exact results. They retain an initial cold query
separately from five warm queries.

| Condition | Baseline median | Candidate median | Tolerance gate |
|---|---:|---:|---|
{table}

Covered warm queries report zero repeated factor discovery. This is bounded
process reuse; it is not an arbitrary-size source construction or full executable
refinement theorem. The supplied wheel paths and commands are retained in the
corresponding `.guard.json` files and frozen acceptance manifest.

## Cross-family and growth evidence

[196](cold-196.log), [Antihydra](cold-antihydra.log), and
[Fermat/Mersenne](cold-special.log) have five-sample fresh installed comparisons.
The original combined [family batch](cold-families.guard.json) and five-pair
[Collatz batch](cold-collatz.guard.json) timed out at 35 seconds. Five separately
guarded Collatz pairs are summarized [here](cold-collatz-pairs.json); their full
measurements do not erase the original batch failures.

The [unchanged growth manifest](growth-manifest/report.json) attempted all
**{len(guards)} trials**, covering horizons 16–1024 with five trials per request.
Guard outcomes: **{counts}**. Final status: **{growth["status"]}**;
`collection_complete={growth["collection_complete"]}`. Missing metric rows remain
missing, not zero. Every worker was capped at 35 seconds/1 GiB; the controller
only serialized and aggregated them.

The manifest measures setup, observation, diagnostics, physical-action counts,
concrete construction counters and retained state. It does not furnish every
requested independent discovery/rendering phase or a complete all-family powered
bound. Unavailable instrumentation and uncovered constructor obligations remain red.

The new prime theories establish numerical Phi, local postorder existence,
prefix restriction and rank/select component laws. The full Python shortcuts,
lease lifecycle, budget/cleanup simulation and unbounded construction bounds are
not certified. Passing these sessions does not discharge the 196, Collatz,
Antihydra or Fermat/Mersenne production refinement gates.
"""
(out / "README.md").write_text(text)
print(json.dumps(summary["growth"]))
