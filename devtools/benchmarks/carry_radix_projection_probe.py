"""Executable padded-radix / cyclotomic carry-field research probe."""

from __future__ import annotations

import json

from devtools.benchmarks.json_support import jsonable
from devtools.experiments.algebra.carry_radix_projection import (
    CarryRadixMetrics,
    carry_radix_projection_metrics,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def _pct(numerator: int, denominator: int) -> str:
    return f"{100.0 * numerator / denominator:.2f}%" if denominator else "0.00%"


def write_results(metrics: CarryRadixMetrics) -> None:
    outdir = ROOT / "results"
    outdir.mkdir(exist_ok=True)
    payload = jsonable(metrics)
    (outdir / "carry_radix_projection_metrics.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )

    reverse = metrics["reverse_add_196"]
    rc = reverse.coverage
    lines = [
        "# Padded carry-radix / cyclotomic projection results",
        "",
        "A fixed-width carry word `d_0...d_(L-1)` is treated as the polynomial",
        "`W(z)=sum_i d_i z^(L-1-i)`.  Evaluating at a radix `b` gives the ordinary",
        "base-`b` integer `W(b)`.  The pair `(L,W(b))` is lossless for binary words,",
        "because `L` restores leading-zero padding.  More importantly, an exact",
        "factor `Phi_m(z) | W(z)` implies `Phi_m(b) | W(b)` for every integer `b`.",
        "Therefore bases 3/5/7/10 are theorem instantiations of one polynomial",
        "factorization, not four independent sources of information.",
        "",
        "## Reverse-add 196",
        "",
        f"Across {reverse.steps} current carry rows, **{rc.rows_with_factor}** rows have at least one",
        f"bounded exact cyclotomic factor and **{rc.fully_cyclotomic_planes}** rows are monomial x cyclotomic",
        (
            "with no nontrivial residual.  The factors cover "
            f"**{rc.factor_degree}/{rc.active_degree} = {_pct(rc.factor_degree, rc.active_degree)}** of active polynomial degree."
        ),
        "",
        "| charge | bits |",
        "|---|---:|",
        f"| raw padded binary planes | {rc.raw_plane_bits:,} |",
        f"| factor every row losslessly | {rc.factorized_description_bits:,} |",
        f"| choose cheaper of raw/factor per row | {rc.selective_description_bits:,} |",
        f"| rows where exact factorization wins | {rc.factorization_wins} |",
        "",
        "So the structure is genuine but sparse globally: bounded factorization is not a",
        "replacement encoding for every row.  It is useful as an optional theorem/compression",
        "channel on selected rows.",
        "",
        "Representative exact factors:",
        "",
        "| step | factors | base-3 | base-5 | base-7 | base-10 |",
        "|---:|---|---:|---:|---:|---:|",
    ]
    for step, _word, factors, evaluations in reverse.sample_bridges:
        factor_text = (
            " ".join(
                f"Phi_{order}" + (f"^{exponent}" if exponent != 1 else "")
                for order, exponent in factors
            )
            or "none"
        )
        values = {radix: value for radix, value in evaluations}
        lines.append(
            f"| {step} | `{factor_text}` | {values[3]:,} | {values[5]:,} | {values[7]:,} | {values[10]:,} |"
        )
    lines += [
        "",
        f"The exact current carry field still has **{reverse.exact_current_rows}** classes,",
        f"**{reverse.repeated_current_rows}** repeat, and **{reverse.different_next_conflicts}**",
        "same-current/different-next conflict.  The compact factor-only feature has",
        f"**{reverse.factor_feature_classes}** classes and **{reverse.factor_feature_conflicts}** next conflicts.",
        "Because the step-10/11 collision is already an equality of the *entire* carry row,",
        "no lossless radix evaluation or factorization of that row can make it Markov.",
        "",
        "## Collatz multiply-by-3 carry planes",
        "",
        "The synthesized carries are ternary (`0..2`).  Each row is reversibly represented",
        "for analysis as one scalar offset plus binary bit planes; those planes are not retained",
        "by the canonical compiler.",
        "",
        "| seed | source radix | rows | factor-degree coverage | raw plane bits | factor-all bits | exact factor wins |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for item_1 in metrics["collatz"]:
        c = item_1.coverage
        lines.append(
            f"| {item_1.parameter} | {item_1.source_radix} | {c.rows} | "
            f"{_pct(c.factor_degree, c.active_degree)} | {c.raw_plane_bits:,} | "
            f"{c.factorized_description_bits:,} | {c.factorization_wins} |"
        )
    lines += [
        "",
        "Cyclotomic degree coverage is often strong, especially in larger source radices, but",
        "the explicit factor metadata/residual is usually more expensive than the small carry",
        "plane itself.  The existing Collatz valuation/sentinel quotient therefore remains the",
        "canonical representation; carry-plane factors are useful derived certificates and may",
        "be more valuable when composed temporally rather than encoded row-by-row.",
        "",
        "## Fermat / Mersenne normalization-carry planes",
        "",
        "The production special-number arithmetic retains one scalar end-around boundary carry.",
        "The complete internal signed/multi-valued carry row is reconstructed on demand, converted",
        "losslessly to offset + bit planes, and discarded after measurement.",
        "",
        "| family | parameter | rows | carry range | max planes | factor-degree coverage | raw plane bits | selective bits |",
        "|---|---:|---:|---|---:|---:|---:|---:|",
    ]
    for item_2 in metrics["special_trajectories"]:
        c = item_2.coverage
        lines.append(
            f"| {item_2.family} | {item_2.parameter} | {c.rows} | "
            f"{item_2.min_carry}..{item_2.max_carry} | {item_2.max_bit_planes} | "
            f"{_pct(c.factor_degree, c.active_degree)} | {c.raw_plane_bits:,} | "
            f"{c.selective_description_bits:,} |"
        )
    lines += [
        "",
        "The factor coverage drops as the tested Fermat/Mersenne widths grow.  Local rows can",
        "still compress, but this is not evidence of a bounded full-state quotient.",
        "",
        "### Exhaustive closure check",
        "",
        "| family | parameter | states | exact carry classes | exact target? | exact next? | factor classes | factor target? | factor next? |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for item_3 in metrics["special_closure"]:
        lines.append(
            f"| {item_3.family} | {item_3.parameter} | {item_3.source_states} | "
            f"{item_3.exact_carry_classes} | {item_3.exact_target_separating} | {item_3.exact_next_closed} | "
            f"{item_3.cyclotomic_feature_classes} | {item_3.cyclotomic_target_separating} | "
            f"{item_3.cyclotomic_next_closed} |"
        )
    lines += [
        "",
        "### Does carry structure help a lossy digit channel?",
        "",
        "The strongest test combines one deliberately small current-digit channel (`Phi_2` modulo 4)",
        "with the lossy carry-factor feature, then checks target separation and exact successor closure.",
        "",
        "| family | parameter | states | combined classes | target? | next? | minimized observer classes |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for item_4 in metrics["special_combined_observers"]:
        minimized = item_4.minimized_observer_classes
        lines.append(
            f"| {item_4.family} | {item_4.parameter} | {item_4.source_states} | "
            f"{item_4.combined_classes} | {item_4.target_separating} | {item_4.next_closed} | "
            f"{minimized if minimized is not None else '-'} |"
        )
    lines += [
        "",
        "There is one genuine small positive: for M5, `Phi_2 mod 4 + carry factors` gives a non-injective",
        "29-class closed refinement, and exact unary Moore minimization of that quotient recovers the known",
        "**5 observer classes**.  But it does not generalize: M7, M11 and M13 remain non-next-closed, and",
        "F3 still fails target separation.  A broader single-channel search over `Phi_2..Phi_16` and",
        "coefficient moduli 2/4/8/16/32 found no non-injective closed combination for F3 or M7.",
        "",
        "This is the decisive negative result for the special-number carry hypothesis as a general solution.  For F3,",
        "even the complete internal carry row fails both target separation and next closure.  For",
        "M5/M7 it separates the current target but is not next-closed.  A lossless alternate-radix",
        "reinterpretation of exactly that row cannot improve either fact.  The remaining Fermat/",
        "Mersenne task is still extraction of the small Moore observer from the modular digit field,",
        "not reconstruction of a larger carry vector.",
        "",
        "## Architectural conclusion",
        "",
        "The padded-radix idea is retained as a **derived projection algebra**, not parallel state:",
        "",
        "- exact width + radix evaluation provides reversible leading-zero-safe integer coordinates;",
        "- exact cyclotomic factors are base-independent polynomial facts and can be evaluated in any radix;",
        "- ternary/signed carry fields share one reversible offset+bit-plane adapter;",
        "- lossless factorization always retains an explicit residual;",
        "- canonical Collatz and special-number compiler state remains unchanged.",
        "",
        "The most promising next experiment is temporal composition of the short factor/order",
        "spectra (plus width/growth) and testing whether that history can supply the missing small",
        "reverse-add hidden-source observer.  For special numbers, the M5 bridge suggests searching",
        "direct synthesis maps from digit/carry theorem channels to Moore classes, but the M7+ closure",
        "failures show that row-wise factorization alone is not a scalable solution.",
    ]
    (
        report_output(
            "devtools.benchmarks.carry_radix_projection_probe",
            "CARRY_RADIX_PROJECTION_RESULTS.md",
        )
    ).write_text("\n".join(lines) + "\n")


def main() -> CarryRadixMetrics:
    metrics = carry_radix_projection_metrics()
    write_results(metrics)
    return metrics


if __name__ == "__main__":
    result = main()
    reverse = result["reverse_add_196"]
    print(
        "reverse196",
        reverse.coverage.rows_with_factor,
        reverse.coverage.factor_degree,
        reverse.coverage.active_degree,
        reverse.different_next_conflicts,
    )
    print("collatz profiles", len(result["collatz"]))
    print("special closure profiles", len(result["special_closure"]))
