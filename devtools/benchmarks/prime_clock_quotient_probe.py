"""Deterministic recursive prime-clock wheel quotient probe."""

from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.experiments.primes.prime_clock_quotients import (
    metrics_as_jsonable,
    prime_clock_wheel_audits,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def main() -> int:
    rows = prime_clock_wheel_audits()
    data = metrics_as_jsonable(rows)
    out = report_directory("devtools.benchmarks.prime_clock_quotient_probe")
    out.mkdir(exist_ok=True)
    (out / "prime_clock_quotient_metrics.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n"
    )
    lines = [
        "# Prime-clock recursive wheel quotient results — v0.43.0",
        "",
        "For old wheel modulus `M` and next prime `q`, deletion phase obeys `kappa_(i+1)=kappa_i-M^-1*g_i (mod q)`. The canonical morphism keeps only endpoint phase plus the exact deletion histogram modulo the uniform `Phi_q` direction; endpoint differences and half-gap radix coordinates generate the same action.",
        "",
        "| M | add q | old gaps | new gaps | phase itinerary bits | circular bits | max deviation | endpoint-diff | half-gap | q-power uniform | extension exact |",
        "|---:|---:|---:|---:|---:|---:|---:|---|---|---|---|",
    ]
    for r in rows:
        lines.append(
            f"| {r.old_modulus:,} | {r.new_prime} | {r.old_gap_states:,} | {r.new_gap_states:,} | {r.phase_itinerary_bits:,} | {r.circular_quotient_bits:,} | {r.max_histogram_deviation} | {r.endpoint_difference_exact} | {r.half_gap_radix_exact} | {r.q_power_phase_identity and r.q_power_histogram_uniform} | {r.extension_exact} |"
        )
    lines += [
        "",
        "This remains the positive prime result. The unresolved operation is random-access rank/select through recursively nested wheel morphisms without expanding the old gap cycle.",
        "",
    ]
    (
        report_output(
            "devtools.benchmarks.prime_clock_quotient_probe",
            "PRIME_CLOCK_QUOTIENT_RESULTS.md",
        )
    ).write_text("\n".join(lines))
    print(json.dumps(data, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
