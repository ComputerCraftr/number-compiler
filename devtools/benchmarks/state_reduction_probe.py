from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.experiments.algebra.state_reduction import (
    metrics_as_jsonable,
    state_reduction_metrics,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def main() -> int:
    metrics = state_reduction_metrics()
    payload = metrics_as_jsonable(metrics)
    (
        report_directory("devtools.benchmarks.state_reduction_probe")
        / "state_reduction_metrics.json"
    ).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    lines = [
        "# Exact state reductions and cross-domain propagation (v0.43.0)",
        "",
        "The release distinguishes exact local/action reductions from closed temporal quotients.",
        "A compact current projection is never promoted to successor state unless its transition closes.",
        "",
        "## Reverse-add growth: boundary valuation replaces the carry row",
        "",
        "For symmetric pair polynomial `P`, let `R=P-(b-1)(1+z+...+z^(L-1))` and",
        "`r=v_z(R)`.  The sign of the first nonzero coefficient of `R` is exactly the terminal",
        "carry/growth bit because the final non-neutral reset is its symmetric mirror.",
        "",
        "| base | width | symmetric pair states | growth states | source bits | reduced bits |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in metrics.reverse_growth:
        lines.append(
            f"| {row.base} | {row.width} | {row.symmetric_pair_states:,} | {row.reduced_growth_states:,} | {row.source_bits} | {row.reduced_bits} |"
        )
    r = metrics.reverse196
    lines += [
        "",
        f"On 196/{r.steps} steps: max pair width **{r.max_pair_width}**, max growth-state charge **{r.max_growth_state_bits} bits**,",
        f"max full reset-signature charge **{r.max_reset_signature_bits} bits**, max canonical half-pair payload **{r.max_full_pair_bits} bits**.",
        f"Growth differential exact: **{r.exact_growths}**.",
        "",
        "The boundary state is intentionally not a full successor state.  Cross-seed closure gives",
        f"**{metrics.reverse_growth_closure.successor_conflicts:,} conflicts** over {metrics.reverse_growth_closure.seeds} seeds x {metrics.reverse_growth_closure.steps} steps.",
        "",
        "## Collatz: valuation is the exact accelerated action/position state",
        "",
    ]
    c = metrics.collatz
    lines += [
        f"Across {c.odd_sources:,} odd sources through {c.max_source:,}, only **{c.distinct_valuation_states}** valuation states occur",
        f"(maximum `k={c.maximum_valuation}`; {c.valuation_state_bits} charged value bits versus {c.source_bits} source bits).",
        "The same `k=v2(3n+1)` determines increase/nonincrease and every cyclotomic shift phase `k mod m`.",
        f"Action differential exact: **{c.exact_actions}**. It is not a closed orbit state: **{c.successor_conflicts:,}** next-valuation conflicts.",
        "",
        "## v0.41 propagation audit",
        "",
        "| domain | v0.40 work | v0.41 work | exact semantic result |",
        "|---|---:|---:|---|",
    ]
    p = metrics.propagation
    lines += [
        f"| 196 bootstrap carry normalization ({p.reverse196_bootstrap_transitions} transitions) | {p.reverse196_v040_carry_scans} scans | **{p.reverse196_v041_carry_scans} scans** | unchanged |",
        f"| prime factor candidates ({p.prime_reference_candidates:,} odd candidates) | {p.prime_v040_factor_candidates:,} | **{p.prime_v041_factor_candidates:,}** | {p.prime_canonical_lanes} canonical lanes |",
        f"| prime factor-generator gcd calls | {p.prime_v040_gcd_calls:,} | **{p.prime_v041_gcd_calls:,}** | {p.prime_summary_count} primes, first offset {p.prime_summary_first} |",
        "| Collatz nested divisibility/lane API | duplicate observer | **deleted** | canonical direct `v2(3n+1)` unchanged |",
        "",
        "The Fermat/Mersenne group-depth theorem does **not** automatically transfer to 196 or Collatz:",
        "their compact growth/valuation projections have successor conflicts, so replacing their real state with a saturated depth counter would be unsound.",
        "For primes, the transferable idea is earlier quotienting of impossible divisor branches and residual-set actions; the odd-candidate parity branch is now removed before gcd work.",
        "",
        "The bounded special-number carrier proof remains single-sourced in `devtools/verification/oracles/special_binary_jump.py`; the obsolete over-refined special character state was deleted rather than propagated.",
    ]
    (
        report_output(
            "devtools.benchmarks.state_reduction_probe", "STATE_REDUCTION_RESULTS.md"
        )
    ).write_text("\n".join(lines) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
