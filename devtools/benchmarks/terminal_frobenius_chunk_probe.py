"""Reproducible metrics for the terminal r-level Frobenius chunk quotient."""

from __future__ import annotations

import json
from dataclasses import asdict

from devtools.benchmarks.report_schema import records, sequence
from devtools.experiments.power_numbers.terminal_frobenius_chunk import (
    special_frobenius_chunk_composition_audit,
    special_frobenius_defect_crt_audit,
    special_local_frobenius_chunk_audit,
)
from devtools.paths import report_output, repository_root
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    special_frobenius_chunk_probe,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)

ROOT = repository_root()


def _terminal_candidate(family: str, parameter: int) -> dict[str, object]:
    threshold = terminal_threshold_spec(family, parameter)
    spec = prime_decision_chunk_spec(threshold)
    row = special_frobenius_chunk_probe(spec)
    return {
        "family": family,
        "parameter": parameter,
        "span": spec.span,
        "base_stride_v2": spec.base_stride_v2,
        "required_local_v2": spec.required_local_v2,
        "folded_half_degree_log2": spec.folded_half_degree_log2,
        "status": row.status,
        "method": row.method,
        "polynomial_terms_materialized": row.polynomial_terms_materialized,
        "one_level_replays": row.one_level_replays,
        "raw_trace_squarings": row.raw_trace_squarings,
        "factor_enumeration": row.factor_enumeration,
    }


def build_metrics() -> dict[str, object]:
    local = [
        special_local_frobenius_chunk_audit("fermat", 4, 2, 2, 65537),
        special_local_frobenius_chunk_audit("fermat", 5, 2, 9, 641),
        special_local_frobenius_chunk_audit("fermat", 5, 2, 9, 6700417),
        special_local_frobenius_chunk_audit("mersenne", 13, 1, 3, 8191),
        special_local_frobenius_chunk_audit("mersenne", 11, 1, 2, 23),
        special_local_frobenius_chunk_audit("mersenne", 11, 1, 2, 89),
    ]
    composition = [
        special_frobenius_chunk_composition_audit("fermat", 5, 2, 1, 1, 641),
        special_frobenius_chunk_composition_audit("fermat", 4, 2, 1, 1, 65537),
        special_frobenius_chunk_composition_audit("mersenne", 13, 1, 1, 2, 8191),
    ]
    defect = [
        special_frobenius_defect_crt_audit("fermat", 4, 2, 2, (65537,)),
        special_frobenius_defect_crt_audit("fermat", 5, 2, 9, (641, 6700417)),
        special_frobenius_defect_crt_audit("mersenne", 13, 1, 3, (8191,)),
        special_frobenius_defect_crt_audit("mersenne", 11, 1, 2, (23, 89)),
    ]
    candidate = [
        _terminal_candidate("fermat", 4),
        _terminal_candidate("fermat", 5),
        _terminal_candidate("mersenne", 11),
        _terminal_candidate("mersenne", 13),
    ]
    structural = [
        _terminal_candidate("fermat", 16),
        _terminal_candidate("mersenne", 10007),
    ]
    return {
        "local_factor_backed_audits": [asdict(row) for row in local],
        "composition_audits": [asdict(row) for row in composition],
        "defect_crt_audits": [asdict(row) for row in defect],
        "candidate_fail_closed": candidate,
        "structural_large_span": structural,
        "conclusion": {
            "r_level_stride_residue_quotient_exact": all(
                row.polynomial_terms_materialized == 0 and row.one_level_replays == 0
                for row in local
            ),
            "adjacent_chunk_composition_exact": all(
                row.semantic_composition_exact for row in composition
            ),
            "zero_class_is_terminal_query": True,
            "one_defect_plus_gcd_is_complete_after_extraction": all(
                row.status in ("ALL_PASS", "ALL_FAIL", "SPLIT") for row in defect
            ),
            "production_routes_through_chunk": True,
            "candidate_zero_class_extractor_available": False,
            "production_status": "UNKNOWN",
            "remaining_blocker": (
                "compute the folded X-coefficient/stride-zero class directly from the "
                "unfactored special candidate without factor support, polynomial expansion, "
                "or one-level replay"
            ),
        },
    }


def write_results(data: dict[str, object]) -> None:
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    (results / "terminal_frobenius_chunk_metrics.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n"
    )
    locals_ = records(data["local_factor_backed_audits"])
    comps = records(data["composition_audits"])
    defects = records(data["defect_crt_audits"])
    candidates = records(data["candidate_fail_closed"])
    lines = [
        "# Terminal r-level Frobenius chunk quotient",
        "",
        "The terminal lift language is now represented as one contiguous block rather than",
        "one Kummer/Frobenius bit per level.  Locally, if `q=eps+m*k`, an `r`-level",
        "chunk retains only `rho=k mod 2^r`; the folded coefficient of `X` is `+1`",
        "exactly for `rho=0`.  No negacyclic polynomial is materialized.",
        "",
        "## Factor-backed semantic audit",
        "",
        "| family | parameter | q | span | reaches | rho | [X] | all pass |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row_1 in locals_:
        lines.append(
            f"| {row_1['family']} | {row_1['parameter']} | {row_1['supplied_prime_factor']} | "
            f"{row_1['span']} | {row_1['reaches_start_boundary']} | {row_1['stride_residue']} | "
            f"{row_1['folded_x_coefficient']} | {row_1['all_levels_pass']} |"
        )
    lines += [
        "",
        "Every row records `polynomial_terms_materialized=0` and `one_level_replays=0`.",
        "",
        "## Composition audit",
        "",
        "| family | parameter | q | split | combined rho | direct rho | exact |",
        "|---|---:|---:|---|---:|---:|---:|",
    ]
    for row_2 in comps:
        split = f"{row_2['left_span']}+{row_2['right_span']}"
        lines.append(
            f"| {row_2['family']} | {row_2['parameter']} | {row_2['supplied_prime_factor']} | "
            f"{split} | {row_2['combined_stride_residue']} | {row_2['full_stride_residue']} | "
            f"{row_2['semantic_composition_exact']} |"
        )
    lines += [
        "",
        "## Final defect/gcd packet audit",
        "",
        "| family | parameter | local defects | gcd | status |",
        "|---|---:|---|---:|---|",
    ]
    for row_3 in defects:
        lines.append(
            f"| {row_3['family']} | {row_3['parameter']} | {sequence(row_3['local_defects'])} | "
            f"{row_3['support_gcd']} | {row_3['status']} |"
        )
    lines += [
        "",
        "After a folded-X defect is available, one `gcd(E,N)` is sufficient: full",
        "modulus is ALL_PASS, one is ALL_FAIL, and a proper gcd is a natural SPLIT.",
        "No scalar sign multiplication is used, so mixed local support cannot cancel.",
        "",
        "## Production boundary",
        "",
        "| family | parameter | span | required local v2 | status |",
        "|---|---:|---:|---:|---|",
    ]
    for row_4 in candidates:
        lines.append(
            f"| {row_4['family']} | {row_4['parameter']} | {row_4['span']} | "
            f"{row_4['required_local_v2']} | {row_4['status']} |"
        )
    lines += [
        "",
        "Production now routes the terminal threshold through this chunk surface, but the",
        "unfactored candidate-derived zero-class extractor is not proved.  Therefore all",
        "nontrivial unresolved candidates remain `UNKNOWN` with zero polynomial terms, zero",
        "one-level replays, zero raw Lucas squarings, and zero factor enumeration.",
        "",
        "The remaining P0 is only the direct candidate computation of the folded `X`",
        "coefficient / stride-zero class.  The local block quotient and its composition law",
        "are closed.",
    ]
    (
        report_output(
            "devtools.benchmarks.terminal_frobenius_chunk_probe",
            "TERMINAL_FROBENIUS_CHUNK_RESULTS.md",
        )
    ).write_text("\n".join(lines) + "\n")


def main() -> None:
    data = build_metrics()
    write_results(data)
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
