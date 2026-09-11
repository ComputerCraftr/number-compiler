#!/usr/bin/env python3
"""Reproducible projective-Cayley / Frobenius-wreath research metrics."""

from __future__ import annotations

import json

from devtools.experiments.power_numbers.terminal_projective_wreath import (
    candidate_frobenius_section_probe,
    local_frobenius_wreath_audit,
    projective_lucas_audit,
)
from devtools.paths import report_output, repository_root
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)

ROOT = repository_root()
OUT = ROOT / "results" / "terminal_projective_wreath_metrics.json"
REPORT = report_output(
    "devtools.benchmarks.terminal_projective_wreath_probe",
    "TERMINAL_PROJECTIVE_WREATH_RESULTS.md",
)


def main() -> None:
    local_cases = [
        ("fermat", 4, 65537),
        ("fermat", 5, 641),
        ("fermat", 5, 6700417),
        ("mersenne", 13, 8191),
        ("mersenne", 11, 23),
        ("mersenne", 11, 89),
    ]
    local = []
    for fam, par, q in local_cases:
        chunk = prime_decision_chunk_spec(terminal_threshold_spec(fam, par))
        row = local_frobenius_wreath_audit(fam, par, chunk.start_level, chunk.span, q)
        local.append(
            row.__dict__
            if hasattr(row, "__dict__")
            else {field: getattr(row, field) for field in row.__dataclass_fields__}
        )

    projective_cases = [
        ("fermat", 4, 14),
        ("fermat", 5, 12),
        ("mersenne", 13, 11),
        ("mersenne", 11, 9),
    ]
    projective = []
    for fam, par, steps in projective_cases:
        projective_row = projective_lucas_audit(fam, par, steps)
        projective.append(
            {
                field: getattr(projective_row, field)
                for field in projective_row.__dataclass_fields__
            }
        )

    structural = []
    for fam, par in (("fermat", 16), ("mersenne", 10007)):
        spec = terminal_threshold_spec(fam, par)
        chunk = prime_decision_chunk_spec(spec)
        section_row = candidate_frobenius_section_probe(
            fam, par, chunk.start_level, chunk.span
        )
        structural.append(
            {
                "family": fam,
                "parameter": par,
                "start_level": chunk.start_level,
                "span": chunk.span,
                "span_description_bits": chunk.span.bit_length(),
                "status": section_row.status,
                "method": section_row.method,
                "tree_nodes_materialized": section_row.tree_nodes_materialized,
                "one_level_replays": section_row.one_level_replays,
            }
        )

    data = {
        "projective": projective,
        "local_wreath": local,
        "structural_fail_closed": structural,
        "conclusion": {
            "projective_cayley_exact": all(x["cayley_commutes"] for x in projective),
            "difference_clock_exact": all(
                x["difference_clock_exact"] for x in projective
            ),
            "conditional_section_formula_exact": all(
                x["conditional_section_formula_exact"] for x in local
            ),
            "candidate_derived_section_available": False,
            "production_change": False,
        },
    }
    OUT.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Terminal projective-Cayley / Frobenius-wreath research",
        "",
        "The nonlinear projective quotient is exact:",
        "",
        "```text",
        "t=(x-2)/(x+2)=A/B",
        "(A:B) -> (4AB:(A+B)^2)",
        "S=A+B, D=B-A -> (2S^2-D^2, D^2)",
        "```",
        "",
        "Thus `D` is a known dyadic square clock.  This representation is division-free and any target/nonunit packet can be exposed by gcds, but the simple projective target gcd does not by itself classify the composite controls.",
        "",
        "## Exact local wreath section",
        "",
        "For local stride `k`, Frobenius is the binary odometer:",
        "",
        "```text",
        "tau_(2a)   = (tau_a,tau_a)",
        "tau_(2a+1) = (tau_a,tau_(a+1)) sigma",
        "```",
        "",
        "When the current lift passes (`k` even), the conditional section is exactly `k/2`, the stride at the doubled boundary.  Hence `Section(Frob_m)=Frob_(2m)` is proved locally without materializing the tree.",
        "",
        "| family | parameter | q | start | span | root | next section | direct next | exact | all pass |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---|---|",
    ]
    for report_row in local:
        lines.append(
            f"| {report_row['family']} | {report_row['parameter']} | {report_row['supplied_prime_factor']} | "
            f"{report_row['start_level']} | {report_row['span']} | {report_row['root_permutation']} | "
            f"{report_row['next_boundary_stride']} | {report_row['direct_next_boundary_stride']} | "
            f"{report_row['conditional_section_formula_exact']} | {report_row['chunk_all_pass']} |"
        )
    lines += [
        "",
        "## Boundary",
        "",
        "The section *law* is closed; the candidate-derived section constructor is not.  The unfactored production candidate still does not supply the local odometer section, so no production selector is promoted.  The next theorem is now specifically to realize this conditional section in the sparse principal quotient with unit normalization / natural gcd emission.",
        "",
    ]
    REPORT.write_text("\n".join(lines))
    print(json.dumps(data["conclusion"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
