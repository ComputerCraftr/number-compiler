"""Reproduce the v0.23 projection-output algebra measurements."""

from __future__ import annotations

import json

from devtools.benchmarks.json_support import jsonable
from devtools.experiments.algebra.projection_field_dynamics import (
    projection_field_metrics,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def main() -> None:
    metrics = projection_field_metrics()
    outdir = ROOT / "results"
    outdir.mkdir(exist_ok=True)
    (outdir / "projection_field_metrics.json").write_text(
        json.dumps(jsonable(metrics), indent=2, sort_keys=True) + "\n"
    )
    r = metrics["reverse_add"]
    c = metrics["collatz"]
    p = metrics["primes"]
    _s = metrics["special_digit_features"]
    lines = [
        "# Projection-field algebra results",
        "",
        "v0.23 applies radix/cyclotomic/binomial algebra to projection **outputs**, not only source growth state.",
        "",
        "## Reverse-add output closure",
        "",
        "| seed | steps | exact current actions | repeats | different-next conflicts | transformed-feature conflicts |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for reverse in r:
        lines.append(
            f"| {reverse.seed} | {reverse.steps} | {reverse.exact_actions} | {reverse.repeated_actions} | {reverse.conflicting_next_actions} | {reverse.transformed_feature_conflicts} |"
        )
    lines += [
        "",
        "Seed 196 supplies an exact counterexample to projection-only Markov closure: the same current carry-action projection occurs at consecutive steps but has different next projections.  Lossless re-encodings of that same output cannot fix the missing hidden-source information.",
        "",
        "## Collatz valuation output",
        "",
        "| seed | symbols | runs | sum(k) | raw bits | RLE bits | theorem bits | exact slab bits | slab comps |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for collatz in c:
        lines.append(
            f"| {collatz.seed} | {collatz.valuation_symbols} | {collatz.valuation_runs} | {collatz.valuation_sum} | {collatz.raw_symbol_bits} | {collatz.rle_description_bits} | {collatz.theorem_channel_bits} | {collatz.exact_slab_bits} | {collatz.exact_slab_compositions} |"
        )
    lines += [
        "",
        "Equal valuation runs power in logarithmic composition depth and fixed odd-modulus affine projections are constant-size.  The exact slab payload still grows with independent itinerary information.",
        "",
        "## Prime output fields emitted pre-bitmap",
        "",
        "| candidates | primes | first | least-factor runs | least-factor RLE bits | Boolean theorem bits | theorem comps | decision nodes | charged research projection work |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for prime in p:
        lines.append(
            f"| {prime.length} | {prime.primes} | {prime.first} | {prime.least_factor_runs} | {prime.least_factor_rle_bits} | {prime.boolean_theorem_bits} | {prime.projection_field_compositions} | {prime.decision_nodes} | {prime.charged_projection_work} |"
        )
    lines += [
        "",
        "The least-factor label field is nearly run-incompressible, while the prime Boolean primary/binomial/cyclotomic theorem channels remain small and can be emitted directly from the residual-divisor DAG.  They are optional because they add charged work when `(count, first)` alone is requested.",
        "",
        "## Fermat / Mersenne projection-value closure",
        "",
        "Small individual cyclotomic digit channels merge residue states, but they fail target separation or next-step closure.  On the bounded exact audits, combining enough primary/binomial/cyclotomic channels to make the target exact and next-closed becomes injective, reconstructing the full residue state.  The already-known Moore target observer remains small; extracting its class cheaply is the blocker.",
        "",
    ]
    (
        report_output(
            "devtools.benchmarks.projection_field_probe", "PROJECTION_FIELD_RESULTS.md"
        )
    ).write_text("\n".join(lines) + "\n")
    print(json.dumps(jsonable(metrics), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
