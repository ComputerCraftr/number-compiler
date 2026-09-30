from __future__ import annotations

import json

from devtools.experiments.algebra.digit_cyclotomic_unification import (
    metrics_as_jsonable,
    unified_digit_cyclotomic_metrics,
)
from devtools.paths import report_directory, report_output, repository_root

ROOT = repository_root()


def main() -> int:
    metrics = unified_digit_cyclotomic_metrics()
    payload = metrics_as_jsonable(metrics)
    out = (
        report_directory("devtools.benchmarks.digit_cyclotomic_unification_probe")
        / "digit_cyclotomic_unification_metrics.json"
    )
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Unified source-digit cyclotomic algebra (v0.43.0 cleanup refresh)",
        "",
        "The cyclotomic algebra now sits below projection/carry instrumentation. `CyclotomicDigitBlock`",
        "is the one canonical implementation for source digits, output jets, and quotient blocks, so",
        "actual digit/pair fields no longer have fragmented quotient arithmetic.",
        "",
        f"One canonical digit/cyclotomic block, legacy aliases absent: **{metrics.single_canonical_digit_block}**.",
        f"Cross-family exactness audit: **{metrics.all_exact}**.",
        "",
        "## Normalization is the shared `base-z` morphism",
        "",
        "For `A-D=(base-z)Q+boundary`, a component can reconstruct its carry residue whenever",
        "`base-z` is a unit.  Equivalently the quotient divisor evaluated at `base` is invertible",
        "in the coefficient modulus.  Over `mod 32`:",
        "",
        "| radix | unit orders | singular orders |",
        "|---:|---|---|",
    ]
    for normalization_units_row in metrics.normalization_units:
        lines.append(
            f"| {normalization_units_row.base} | {','.join(map(str, normalization_units_row.unit_orders)) or '-'} | "
            f"{','.join(map(str, normalization_units_row.singular_orders)) or '-'} |"
        )
    lines += [
        "",
        "Every tested channel for the even radices 2/4/10/16 is a 2-adic unit.  Ternary is different:",
        "its power-of-two cyclotomic orders are singular.  Thus binary Collatz makes the 2-adic",
        "carry spectrum entirely derived from source/raw/normalized digit components, while ternary",
        "can retain genuine normalization-kernel information in those channels.",
        "",
        "## Exact cross-family adapter audit",
        "",
        "| family | cases | components | exact | unit normalizations | carries recovered |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for family_audit_row in metrics.family_audit:
        lines.append(
            f"| {family_audit_row.family} | {family_audit_row.cases} | {family_audit_row.components} | {family_audit_row.exact_components} | "
            f"{family_audit_row.unit_normalizations} | {family_audit_row.recovered_carry_components} |"
        )
    lines += [
        "",
        "The adapters exercise actual reverse-add digit reflection/pairing, radix-polynomial Collatz",
        "`3n+1`, Lucas-Lehmer cyclic square/add, and Pepin negacyclic squaring through the same block.",
        "",
        "## Carry dependency on long real trajectories",
        "",
        "| family | radix | steps | orders | components | unit | recovered |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for carry_dependency_row in metrics.carry_dependency:
        lines.append(
            f"| {carry_dependency_row.family} | {carry_dependency_row.base} | {carry_dependency_row.steps} | {carry_dependency_row.orders} | {carry_dependency_row.components} | "
            f"{carry_dependency_row.unit_components} | {carry_dependency_row.recovered_components} |"
        )
    lines += [
        "",
        "For reverse-add 196/base-10 and binary Collatz, all tested `mod 32` carry components are",
        "algebraically reconstructed.  They must therefore not be retained as independent cyclotomic",
        "observer state.  Ternary Collatz intentionally shows the singular exception.",
        "",
        "## Deeper finite-field cyclotomic factors",
        "",
        "A whole `Phi_m mod p` block now splits lazily into irreducible factors and reconstructs exactly",
        "by polynomial CRT.  This exposes much smaller primary components:",
        "",
        "| family | parameter | p | order | whole degree | factors | factor degree |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for factor_splits_row in metrics.factor_splits:
        lines.append(
            f"| {factor_splits_row.family} | {factor_splits_row.parameter} | {factor_splits_row.coefficient_prime} | {factor_splits_row.cyclotomic_order} | "
            f"{factor_splits_row.whole_degree} | {factor_splits_row.factor_count} | {factor_splits_row.factor_degree} |"
        )
    lines += [
        "",
        (
            f"In particular `Phi_31 mod 2` is **{metrics.mersenne31_factor_count} degree-"
            f"{metrics.mersenne31_factor_degree} factors**, rather than one opaque degree-30 block."
        ),
        "",
        "## Normalization can couple primary factors back together",
        "",
        "| family | parameter | p | selected factors | classes | conflicts | target separating |",
        "|---|---:|---:|---|---:|---:|---:|",
    ]
    for factor_closure_row in metrics.factor_closure:
        lines.append(
            f"| {factor_closure_row.family} | {factor_closure_row.parameter} | {factor_closure_row.coefficient_prime} | "
            f"{','.join(map(str, factor_closure_row.selected_factors))} | {factor_closure_row.classes} | {factor_closure_row.conflicts} | "
            f"{factor_closure_row.target_separating} |"
        )
    lines += [
        "",
        "M7 is the clean warning: each degree-3 factor has only 8 states but fails successor closure;",
        "both factors together give the exact 64-class sign quotient.  F3 over `F_3` is harsher:",
        "each degree-4 factor fails, while both together reconstruct all 257 integer states.  Finite",
        "factorization is therefore a discovery/quotient tool, not automatic dynamical independence.",
        "",
        "## Architectural consequence",
        "",
        "The search order is now `source digits -> cyclotomic primary components -> raw operator ->",
        "normalization morphism -> target/next closure`.  Carry factors are synthesized from this path",
        "when invertible; separate carry-cyclotomic state is forbidden unless the normalization map is",
        "singular and an exact observer theorem requires its kernel/cokernel information.",
    ]
    (
        report_output(
            "devtools.benchmarks.digit_cyclotomic_unification_probe",
            "DIGIT_CYCLOTOMIC_UNIFICATION_RESULTS.md",
        )
    ).write_text("\n".join(lines) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
