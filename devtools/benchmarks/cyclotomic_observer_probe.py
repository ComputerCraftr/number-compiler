"""Executable normalization-defect / cyclotomic-observer research probe."""

from __future__ import annotations

import json

from devtools.benchmarks.json_support import jsonable
from devtools.experiments.algebra.cyclotomic_observer import (
    CyclotomicObserverMetrics,
    cyclotomic_observer_metrics,
)
from devtools.paths import report_directory, report_output, repository_root

ROOT = repository_root()


def _pct(value: float) -> str:
    return f"{100.0 * float(value):.2f}%"


def write_results(metrics: CyclotomicObserverMetrics) -> None:
    payload = jsonable(metrics)
    outdir = report_directory("devtools.benchmarks.cyclotomic_observer_probe")
    outdir.mkdir(exist_ok=True)
    (outdir / "cyclotomic_observer_metrics.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )

    jet = metrics["jet_unification"]
    defect = metrics["normalization_defect"]
    reverse = metrics["reverse_add_196"]
    temporal = metrics["reverse_temporal"]
    lines = [
        "# Cyclotomic-jet / normalization-observer results",
        "",
        "This pass treats carry structure as an exact normalization **defect algebra**, not as",
        "another retained carry encoding.  If raw coefficients `A(z)`, normalized digits `D(z)`,",
        "and carry boundaries `c_0..c_L` obey `a_i+c_i=d_i+b*c_(i+1)`, then with",
        "`Q(z)=sum_i c_(i+1) z^i` the canonical finite identity is",
        "",
        "```text",
        "A(z)-D(z) = (b-z) Q(z) - c_0 + c_L z^L.",
        "```",
        "",
        "The boundary term vanishes literally for a zero-ended finite normalization and vanishes",
        "in the quotient ring for cyclic/negacyclic end-around normalization.  Therefore every",
        "cyclotomic projection of a carry row is a projection of one exact normalization theorem.",
        "",
        "## One canonical cyclotomic jet",
        "",
        "The new `CyclotomicDigitBlock(order, power, modulus)` is reduction modulo",
        "`(Phi_order(z)^power, modulus)`.  It subsumes the previously separate local channels:",
        "",
        f"- `Phi_1^(r)` local coefficients equal the binomial moments: **{jet.phi1_equals_binomial}**;",
        f"- `Phi_2^(r)` local coefficients equal the primary `z+1` jet: **{jet.phi2_equals_primary}**;",
        "- `power=1` is the existing cyclotomic-residue channel.",
        "",
        "Legacy `CyclotomicJetBlock` / `CyclotomicProjectionBlock` names are absent;",
        "`CyclotomicDigitBlock` is the sole canonical implementation and cache identity.",
        "",
        "## Exact normalization-defect audit",
        "",
        "| family/path | exact cases |",
        "|---|---:|",
        f"| reverse-add 196 finite blocks | {defect.reverse_steps} |",
        f"| reverse-add zero-boundary padded blocks | {defect.reverse_zero_boundary_padded_steps} |",
        f"| Collatz multiply-3/add-1 fields (radices 4/10/16) | {defect.collatz_steps} |",
        f"| Mersenne cyclic states (M5 ring) | {defect.cyclic_states} |",
        f"| Fermat negacyclic states (width 4 ring) | {defect.negacyclic_states} |",
        "",
        f"All boundary-aware identities and selected quotient-ring projections agree: **{defect.exact}**.",
        "",
        "## Reverse-add: explain the 196 collision, then reject fake closure",
        "",
        f"The first exact same-action/different-successor collision remains steps **{reverse.collision_steps[0]}** and **{reverse.collision_steps[1]}**.",
        f"Their complete carry rows are equal: **{reverse.collision_carry_equal}**.  The existing",
        f"base-`(b-1)` source residue separates them as **{reverse.collision_base_minus_residues[0]} vs {reverse.collision_base_minus_residues[1]} (mod 9)**.",
        "That is exactly the `Phi_1`/digit-sum coordinate already represented in the canonical",
        "residue interface, so no duplicate jet identity is retained for it.",
        "",
        f"A bounded search tested **{reverse.candidate_count}** single cyclotomic jets (`Phi_1..Phi_12`,",
        "powers 1..3 where degree <=12, coefficient moduli 2/4/8/16) together with the carry action.",
        f"**{reverse.zero_conflict_candidates}** are conflict-free on the single 196 orbit, but",
        f"**{reverse.zero_conflict_noninjective_candidates}** are non-injective.  The minimum closed",
        f"candidate still has **{reverse.minimum_zero_conflict_classes} classes for 256 transitions**:",
        "the apparent solutions reconstructed the trajectory rather than finding a quotient.",
        "",
        "The existing small residue channels also fail cross-seed closure:",
        f"base-`(b-1)` gives **{reverse.neighboring_base_minus_conflicts}** conflicts and",
        f"base-`(b-1)` + base-`(b+1)` gives **{reverse.neighboring_base_pm_conflicts}** on seeds 190..202.",
        "",
        "### Finite-memory test",
        "",
        f"Across seeds {temporal.seed_start}..{temporal.seed_stop} for {temporal.steps} steps, short histories reduce",
        "conflicts but do not close:",
        "",
        "| history | base-(b-1) classes | conflicts | base±1 classes | conflicts |",
        "|---:|---:|---:|---:|---:|",
    ]
    for minus, pm in zip(temporal.base_minus, temporal.base_pm, strict=True):
        lines.append(
            f"| {minus.history} | {minus.classes:,} | {minus.conflicts:,} | "
            f"{pm.classes:,} | {pm.conflicts:,} |"
        )
    lines += [
        "",
        f"An apparent higher-order winner, `Phi_{temporal.apparent_jet_order} mod {temporal.apparent_jet_modulus}` + carry action,",
        f"has **0 conflicts** on seeds 1..{temporal.training_seed_stop} for {temporal.training_steps} steps",
        f"({temporal.training_classes:,} observed classes) but fails with **{temporal.holdout_conflicts}** conflict on the",
        f"disjoint seeds {temporal.holdout_seed_start}..{temporal.holdout_seed_stop} for {temporal.holdout_steps} steps.",
        "It is therefore kept as research evidence of overfitting, not promoted into canonical state.",
        "",
        "## Special-number square-sign quotient",
        "",
        "Both special recurrences square before their next observation, so `x` and `-x` have the",
        "same successor.  For Mersenne width `p`, the binary digit polynomial modulo `Phi_p` over",
        "`F_2` has kernel exactly the all-ones word; hence its equivalence classes are exactly",
        "bitwise complements, i.e. `x ~ -x mod (2^p-1)`.  This turns the earlier M5 empirical",
        "carry bridge into a family-level algebraic quotient:",
        "",
        "| p | states | Phi_p mod 2 classes | sign classes | same partition | target? | next-closed? |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for item_1 in metrics["mersenne_phi_sign"]:
        lines.append(
            f"| {item_1.exponent} | {item_1.states:,} | {item_1.phi_classes:,} | "
            f"{item_1.sign_classes:,} | {item_1.same_partition} | "
            f"{item_1.target_separating} | {item_1.next_closed} |"
        )
    lines += [
        "",
        "Pepin squaring has the same sign-erasure property modulo `2^(2^n)+1`; because its current",
        "target is `-1` while `+1` is sign-equivalent, the safe observer is `(current_target_bit,",
        "sign_representative)` rather than the representative alone.",
        "",
        "| family | parameter | source states | sign-quotient classes | target? | next-closed? |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for item_2 in metrics["special_sign_quotients"]:
        lines.append(
            f"| {item_2.family} | {item_2.parameter} | {item_2.source_states:,} | "
            f"{item_2.quotient_classes:,} | {item_2.target_separating} | {item_2.next_closed} |"
        )
    lines += [
        "",
        "These are exact observer theorems for the tested prime moduli, not lookup-table labels.",
        "Composite Mersenne moduli are intentionally excluded from the prime-group theorem.",
        "",
        "## Production work reduction from sign canonicalization",
        "",
        "The special digit-field projector now canonicalizes each squaring input to the sparser of",
        "`x` and `-x` before convolution.  This preserves the exact recurrence result and reduces",
        "actual digit-product work without retaining a parallel sign state:",
        "",
        "| family | parameter | scalar products old -> new | reduction | coefficient adds old -> new | reduction | changed steps | nonzero digits saved |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for item_3 in metrics["special_sign_work"]:
        scalar_red = (
            1.0 - item_3.quotient_scalar_products / item_3.baseline_scalar_products
        )
        add_red = (
            1.0
            - item_3.quotient_coefficient_additions
            / item_3.baseline_coefficient_additions
        )
        lines.append(
            f"| {item_3.family} | {item_3.parameter} | {item_3.baseline_scalar_products:,} -> "
            f"{item_3.quotient_scalar_products:,} | {_pct(scalar_red)} | "
            f"{item_3.baseline_coefficient_additions:,} -> {item_3.quotient_coefficient_additions:,} | "
            f"{_pct(add_red)} | {item_3.sign_quotient_steps} | {item_3.nonzero_digits_saved} |"
        )
    lines += [
        "",
        "## Architectural conclusion",
        "",
        "- normalization carries now have one exact boundary-aware defect theorem;",
        "- primary jets, binomial moments, and cyclotomic residues share one generalized jet algebra;",
        "- legacy projection-only cyclotomic names are absent rather than parallel state identities;",
        "- reverse-add candidate features must pass cross-seed closure and non-injectivity before promotion;",
        "- special-number squaring uses an algebraically proved sign quotient before convolution;",
        "- the small prime Fermat/Mersenne Moore observers now have direct group-theoretic descriptions;",
        "- derived carry/radix helpers remain outside production compiler reachability.",
        "",
        "The remaining reverse-add problem is therefore narrower: find a source observer smaller than",
        "the pair field that survives the cross-seed closure tests.  More current-row factorization or",
        "longer histories of the existing base±1 residues are now experimentally ruled out as the next",
        "generic solution on the bounded adversarial sets used here.",
    ]
    (
        report_output(
            "devtools.benchmarks.cyclotomic_observer_probe",
            "CYCLOTOMIC_OBSERVER_RESULTS.md",
        )
    ).write_text("\n".join(lines) + "\n")


def main() -> None:
    metrics = cyclotomic_observer_metrics()
    write_results(metrics)
    print(json.dumps(jsonable(metrics), indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
