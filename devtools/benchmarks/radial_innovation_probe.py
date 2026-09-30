"""Deterministic radial-mode / innovation quotient probe."""

from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.experiments.algebra.radial_innovation_quotients import (
    metrics_as_jsonable,
    radial_innovation_metrics,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def main() -> int:
    m = radial_innovation_metrics()
    data = metrics_as_jsonable(m)
    out = report_directory("devtools.benchmarks.radial_innovation_probe")
    out.mkdir(exist_ok=True)
    (out / "radial_innovation_metrics.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n"
    )
    lines = [
        "# Radial-mode / normalized-innovation quotient results — v0.46.0",
        "",
        "## Reverse-add radial theorem",
        "",
        "For a block with `q` no-growth and `r` growth steps the homogeneous pair-field action is `2^q(1+z)^r`; at `z=1` the common physical scale is exactly `2^(q+r)`. In `Phi_(2m)=z^m+1`, the coefficient-content valuation is `q+floor(r/m)`, so the large radial mode is represented only by that valuation and the remaining unit polynomial is binary-powered at reduced precision.",
        "",
        "| m | q | r | radial exp | v2 | r mod m | annihilated | exact multiplier reconstruction |",
        "|---:|---:|---:|---:|---:|---:|---|---|",
    ]
    for multiplier_r in m.multiplier:
        lines.append(
            f"| {multiplier_r.classes} | {multiplier_r.no_growth} | {multiplier_r.growth} | {multiplier_r.radial_exponent} | {multiplier_r.scalar_v2} | {multiplier_r.remainder_growth} | {multiplier_r.annihilated} | {multiplier_r.exact_reconstruction} |"
        )
    lines += [
        "",
        "## Reverse-add live innovation after radial annihilation",
        "",
        "The audit discards the old pair separately in each cyclotomic factor as soon as its multiplier is provably zero. Only the transported forcing innovation remains.",
        "",
        "| domain | modes | usable | innovation classes | distinct pairs | growth conflicts | action conflicts | max live | near reconstruction |",
        "|---|---|---:|---:|---:|---:|---:|---:|---|",
    ]
    for reverse_add_r in m.reverse_add:
        lines.append(
            f"| {reverse_add_r.label} | {','.join(map(str, reverse_add_r.orders))} | {reverse_add_r.usable_states:,} | {reverse_add_r.innovation_classes:,} | {reverse_add_r.distinct_pair_states:,} | {reverse_add_r.next_growth_conflicts:,} | {reverse_add_r.next_action_conflicts:,} | {reverse_add_r.max_live_steps} | {reverse_add_r.near_reconstruction} |"
        )
    lines += [
        "",
        "Low modes expose real finite source-annihilation but retain next-action conflicts. Adding enough modes to close the bounded action approaches one state per distinct pair on holdouts, so the closure path is rejected as source reconstruction. The radial theorem itself remains canonical and useful for proving source death.",
        "",
        "## Reverse-add reversal-fixed symmetry frame",
        "",
        "The width-growth action is quotiented as a two-sector reflection frame. Even-width palindromes first lose their exact `(1+z)` symmetry factor and are then centered; odd-width palindromes are centered directly. The resulting residue is fixed by `z -> z^-1`. The low `Phi_2/Phi_4/Phi_8` views are no longer concatenated as unrelated rings: one `FixedRealCyclotomicGerm` uses `x=z+2+z^-1`, `P8=x^2-4x+2`, and the divided values `Q(0),Q(2)` for `F=R8+P8*Q`. All views are taken at one common source-death horizon. In this frame no-growth acts by `2`, odd-to-even growth by `1`, and even-to-odd growth by `x`.",
        "",
        "| domain | modes | usable | fixed-frame classes | distinct pairs | growth conflicts | action conflicts | max live | near reconstruction |",
        "|---|---|---:|---:|---:|---:|---:|---:|---|",
    ]
    for reverse_add_symmetry_r in m.reverse_add_symmetry:
        lines.append(
            f"| {reverse_add_symmetry_r.label} | {','.join(map(str, reverse_add_symmetry_r.orders))} | {reverse_add_symmetry_r.usable_states:,} | {reverse_add_symmetry_r.innovation_classes:,} | {reverse_add_symmetry_r.distinct_pair_states:,} | {reverse_add_symmetry_r.next_growth_conflicts:,} | {reverse_add_symmetry_r.next_action_conflicts:,} | {reverse_add_symmetry_r.max_live_steps} | {reverse_add_symmetry_r.near_reconstruction} |"
        )
    lines += [
        "",
        "The shared-horizon real germ fixes an implementation error in the former joint audit: individual factors can die at different suffix lengths (a regression witness has horizons `2,6,7`), so combining their earliest-dead residues did not describe one innovation polynomial. The corrected low germ still leaves real action conflicts, while adding `Phi_16` closes bounded guards only at/near reconstruction. Algebraically the invisible low-germ difference is `P8*(2^(w-1), 2^(w-2)*x, x*(x-2))`; the remaining 196 blocker is a proper behavioral quotient of that kernel, not another independent cyclotomic coordinate.",
        "",
        "## Collatz 3-adic radial innovation",
        "",
        "An accelerated valuation slab is exactly `(3^H*x+C)/2^K`. Modulo `3^a`, the source multiplier has valuation `H`; after `a` odd steps it is zero and the current residue is exactly the innovation term. No digit or multiplication carry field is used.",
        "",
        "| domain | precision a | usable | innovation classes | distinct current states | next-v2 conflicts | source dead | projection exact | near reconstruction |",
        "|---|---:|---:|---:|---:|---:|---|---|---|",
    ]
    for collatz_r in m.collatz:
        lines.append(
            f"| {collatz_r.label} | {collatz_r.precision} | {collatz_r.usable_states:,} | {collatz_r.innovation_classes:,} | {collatz_r.distinct_current_states:,} | {collatz_r.next_valuation_conflicts:,} | {collatz_r.source_annihilation_exact} | {collatz_r.innovation_projection_exact} | {collatz_r.near_reconstruction} |"
        )
    lines += [
        "",
        "The 3-adic radial split is an exact finite-memory theorem for local projections, but increasing precision eliminates current-action conflicts only by approaching the current odd state itself. It is therefore retained as a theorem/projection channel, not promoted as the Collatz orbit state.",
        "",
        "## Collatz radix-4 fixed-point frame",
        "",
        "The low radix-4 `1` run is the 2-adic fixed-point frame around `-1/3`: if `n=(4^q-1)/3+4^q m`, then `3n+1=4^q(3m+1)`. The unbounded `q` affects only the current valuation and is removed before testing future closure. The surviving local sector is one bit `t=k mod 2`.",
        "",
        "The next valuation is itself a boundary first-hole query: `v2(9m+4)` for `t=0`, or `v2(9m+5)-1` for `t=1`. v0.46 removes the literal period implementation entirely. A general `RationalPadicRootGerm(-c/3^h)` skips constant radix-4 runs by the valuation of `3c-3^h d`; at the first mismatch `PadicAngularBoundaryGerm` rewrites the normalized discrepancy as an affine map of the unconsumed higher suffix. `CollatzAffineSuffixGerm` then pulls the next root back through that affine map. No period of length `3^(h-1)` or intermediate Collatz digit word is materialized.",
        "",
        "| domain | precision | usable | distinct current | raw future classes | raw future conflicts | fixed-frame classes | fixed-frame conflicts | projection exact | near reconstruction | symbolic nonclosure |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---|---|---|",
    ]
    for collatz_fixed_frame_r in m.collatz_fixed_frame:
        lines.append(
            f"| {collatz_fixed_frame_r.label} | {collatz_fixed_frame_r.precision} | {collatz_fixed_frame_r.usable_states:,} | {collatz_fixed_frame_r.distinct_current_states:,} | {collatz_fixed_frame_r.raw_future_classes:,} | {collatz_fixed_frame_r.raw_future_conflicts:,} | {collatz_fixed_frame_r.frame_future_classes:,} | {collatz_fixed_frame_r.frame_future_conflicts:,} | {collatz_fixed_frame_r.frame_projection_exact} | {collatz_fixed_frame_r.frame_near_reconstruction} | {collatz_fixed_frame_r.finite_precision_nonclosure_witness} |"
        )
    lines += [
        "",
        "This is a real frame quotient: on the disjoint precision-16 guards it removes several hundred redundant 3-adic classes and the sampled future-valuation conflicts fall to zero without crossing the 95% reconstruction guard. It is still not globally closed. For every finite precision `a`, tails `3` and `3+4*3^a` have the same framed residue and sector but next valuations `4` and `1`. The remaining Collatz blocker is therefore temporal composition of the symbolic affine/root branches, not the discarded radix-4 frame depth or a literal periodic root.",
        "",
        "## Collatz rational-root/angular-germ differential audit",
        "",
        f"- odd sources: **{m.collatz_rational_root.odd_sources:,}**",
        f"- projected accelerated steps per source: **{m.collatz_rational_root.projected_steps}**",
        f"- exact against integer Collatz: **{m.collatz_rational_root.exact}**",
        f"- directly checked denominator powers through: **3^{m.collatz_rational_root.max_denominator_power}**",
        f"- million-run first valuation: **{m.collatz_rational_root.million_run_valuation:,}**",
        f"- final unconsumed suffix length after two steps: **{m.collatz_rational_root.million_run_final_suffix_length}**",
        "",
    ]
    (
        report_output(
            "devtools.benchmarks.radial_innovation_probe",
            "RADIAL_INNOVATION_RESULTS.md",
        )
    ).write_text("\n".join(lines))
    print(json.dumps(data, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
