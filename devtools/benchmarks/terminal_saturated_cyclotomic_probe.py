"""Reproducible audit for the saturated/cyclotomic-extension terminal route."""

from __future__ import annotations

import json

from devtools.experiments.power_numbers.terminal_saturated_cyclotomic import (
    candidate_saturated_cyclotomic_probe,
    cyclotomic_factor_audit,
    cyclotomic_witness_cost_audit,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def main() -> None:
    factor_cases = (
        ("fermat", 4, (65537,)),
        ("fermat", 5, (641, 6700417)),
        ("mersenne", 11, (23, 89)),
        ("mersenne", 13, (8191,)),
    )
    rows = []
    for family, parameter, factors in factor_cases:
        a = cyclotomic_factor_audit(family, parameter, factors)
        rows.append(
            {
                "family": family,
                "parameter": parameter,
                "conductor_v2": a.criterion.conductor_v2,
                "frobenius_degree": a.criterion.frobenius_degree,
                "subgroup_residues": a.criterion.subgroup_residues,
                "factor_residues": a.residues,
                "local_passes": a.local_passes,
                "extension_exists_by_factor_truth": a.extension_exists_by_factor_truth,
                "agrees_with_prime_truth": a.agrees_with_prime_truth,
            }
        )
    costs = []
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 16),
        ("mersenne", 13),
        ("mersenne", 10007),
    ):
        cost = cyclotomic_witness_cost_audit(family, parameter)
        costs.append(
            {
                "family": family,
                "parameter": parameter,
                "conductor_v2": cost.criterion.conductor_v2,
                "frobenius_degree": cost.criterion.frobenius_degree,
                "construction_squarings": cost.construction_squarings,
                "order_verification_squarings": cost.order_verification_squarings,
                "total_sequential_squarings": cost.total_sequential_squarings,
                "classical_horizon": cost.classical_horizon,
                "cheaper_than_classical_chain": cost.cheaper_than_classical_chain,
            }
        )
    probes = [
        candidate_saturated_cyclotomic_probe(f, p)
        for f, p in (("fermat", 4), ("fermat", 5), ("mersenne", 11), ("mersenne", 13))
    ]
    out = {
        "factor_semantics": rows,
        "witness_cost": costs,
        "candidate_probes": probes,
        "conclusion": {
            "cyclotomic_extension_existence_matches_terminal_prime_decision": True,
            "fermat_orbit_polynomial_degree": 1,
            "mersenne_orbit_polynomial_degree": 2,
            "degree_one_payload_is_primitive_root": True,
            "degree_two_payload_is_primitive_root_trace": True,
            "compact_candidate_constructor_known": False,
            "production_promotable": False,
        },
    }
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    (results / "terminal_saturated_cyclotomic_metrics.json").write_text(
        json.dumps(out, indent=2, sort_keys=True) + "\n"
    )

    lines = [
        "# Saturated two-power cyclotomic terminal audit",
        "",
        "For the shortened terminal conductor `s=2^v`, classical cyclotomic-extension",
        "existence is exactly the special-number all-local congruence.  Fermat has",
        "`ord_s(N)=1`, hence every factor must be `1 mod s`; Mersenne has",
        "`ord_s(N)=2`, hence every factor must be `+/-1 mod s`.  At the current",
        "square-root/CRT decision thresholds those conditions are equivalent to primality.",
        "",
        "| family | parameter | v | degree | local residues | extension exists |",
        "|---|---:|---:|---:|---|---|",
    ]
    for row_1 in rows:
        lines.append(
            f"| {row_1['family']} | {row_1['parameter']} | {row_1['conductor_v2']} | "
            f"{row_1['frobenius_degree']} | `{row_1['factor_residues']}` | "
            f"{row_1['extension_exists_by_factor_truth']} |"
        )
    lines += [
        "",
        "## Constructor boundary",
        "",
        "The low extension degree does not supply the missing candidate state.  In",
        "the Fermat degree-one case the orbit polynomial is `X-zeta`, so its",
        "coefficient is the primitive `2^v` root itself.  In the Mersenne degree-two",
        "case it is `X^2-TX+1`, where `T=zeta+zeta^-1` is exactly the missing",
        "norm-one Lucas trace.  Constructing these from the fixed special generators",
        "and proving exact order consumes the classical sequential squaring chain:",
        "",
        "| family | parameter | build | verify | total | classical |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for row_2 in costs:
        lines.append(
            f"| {row_2['family']} | {row_2['parameter']} | {row_2['construction_squarings']} | "
            f"{row_2['order_verification_squarings']} | {row_2['total_sequential_squarings']} | "
            f"{row_2['classical_horizon']} |"
        )
    lines += [
        "",
        "Therefore saturated/cyclotomic-extension existence is an exact semantic",
        "reformulation of the desired theorem, but not a new source extractor.  It",
        "cannot be promoted to production without an independent compact constructor",
        "for the primitive root (Fermat) or its trace (Mersenne).",
    ]
    (
        report_output(
            "devtools.benchmarks.terminal_saturated_cyclotomic_probe",
            "TERMINAL_SATURATED_CYCLOTOMIC_RESULTS.md",
        )
    ).write_text("\n".join(lines) + "\n")
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
