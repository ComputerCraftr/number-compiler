"""Cross-coordinate prime projection experiment for v0.15.0."""

from __future__ import annotations

from devtools.paths import report_directory

import json
from typing import TYPE_CHECKING

from devtools.paths import report_output, repository_root
from number_compiler.projection.radix_decision import bitmap_radix_decision_metrics
from number_compiler.sequences.prime.coordinates import (
    prime_block_summary_hyperbolic_packed,
    prime_pair_field,
    project_least_factor_field,
)
from number_compiler.sequences.prime.encoding_analysis import (
    factor_coordinate_period_metrics,
    project_prime_power_radix_metrics,
    zeckendorf_bitmap_decision_metrics,
)
from number_compiler.sequences.prime.set import project_odd_prime_block
from number_compiler.sequences.prime.wheel import (
    BroadwordPackedWheelProgram,
    build_finite_packed_prime_wheel,
    build_lcm_wheel,
    build_packed_wheel_program,
    build_self_modifying_packed_wheel,
    build_squarefree_wheel,
)

if TYPE_CHECKING:
    from number_compiler.sequences.prime.set import PrimeProjection


ROOT = repository_root()


def lane_min_description_bits(
    projection: PrimeProjection,
) -> int:
    return sum(
        max(1, lane.factor.bit_length()) + max(1, lane.phase.bit_length())
        for lane in projection.canonical_lanes
    )


def main() -> None:
    OUT = (
        report_directory("devtools.benchmarks.prime_coordinate_probe")
        / "prime_coordinate_metrics.json"
    )
    DOC = report_output(
        "devtools.benchmarks.prime_coordinate_probe", "PRIME_COORDINATE_RESULTS.md"
    )
    start = 9_999_993
    previous_prime = 9_999_991
    length = 4096
    high = start + 2 * (length - 1)

    base_projection = project_odd_prime_block(start, length)
    least_rows = []
    for n in (16, 64, 256, 1024, 4096):
        p = project_odd_prime_block(start, n)
        lf = project_least_factor_field(start, n)
        fw = build_finite_packed_prime_wheel(start, n)
        least_rows.append(
            {
                "length": n,
                "periodic_lanes": lf.periodic_lanes,
                "active_lanes": lf.active_lane_count,
                "removed_lanes": lf.removed_finite_lanes,
                "active_modulus_bits": fw.modulus_bits,
                "periodic_factor_phase_bits": lane_min_description_bits(p),
                "source_lane_hits": fw.source_lane_hits,
            }
        )

    lcm = build_lcm_wheel(int(high**0.5))
    squarefree = build_squarefree_wheel(int(high**0.5))
    packed = build_packed_wheel_program(int(high**0.5), 63)
    packed_first = packed.first_prime(start, length)
    broadword = BroadwordPackedWheelProgram.build(int(high**0.5))
    hyperbolic = prime_block_summary_hyperbolic_packed(start, length)
    selfmod = build_self_modifying_packed_wheel(int(high**0.5), 62)

    pair_rows = []
    for base in (2, 3, 10, 16, 64):
        field = prime_pair_field(previous_prime, 28, base=base)
        pair_rows.append(
            {
                "base": base,
                "pair_digits": len(field.pair_sums),
                "carry_ones": field.carry_ones,
                "value": field.value,
                "residue_1009": field.residue(1009),
            }
        )

    power_radix = []
    for radix in (2, 4, 8, 16, 64):
        m = project_prime_power_radix_metrics(start, length, radix)
        power_radix.append(
            {
                "radix": radix,
                "digits": m.digits,
                "finite_lanes": m.finite_lanes,
                "reachable_nodes": m.reachable_nodes,
                "reachable_child_refs": m.reachable_child_refs,
                "allocated_nodes": m.allocated_nodes,
                "allocated_child_refs": m.allocated_child_refs,
                "or_calls": m.or_calls,
            }
        )

    binary = bitmap_radix_decision_metrics(
        base_projection.composite_mask, 12, order="msb"
    )
    fib = zeckendorf_bitmap_decision_metrics(
        base_projection.composite_mask, length, order="msb"
    )

    period2 = factor_coordinate_period_metrics(start, length, base=2)
    period64 = factor_coordinate_period_metrics(start, length, base=64)

    assert base_projection.summary.first is not None
    metrics = {
        "start": start,
        "previous_prime": previous_prime,
        "length": length,
        "high": high,
        "next_prime_index": base_projection.summary.first,
        "next_prime": start + 2 * base_projection.summary.first,
        "pair_field": pair_rows,
        "finite_least_factor": least_rows,
        "global_wheels": {
            "limit": squarefree.limit,
            "lcm_bits": lcm.modulus_bits,
            "lcm_update_events": lcm.update_events,
            "squarefree_bits": squarefree.modulus_bits,
            "squarefree_generator_events": squarefree.generator_events,
            "periodic_factor_phase_bits_4096": lane_min_description_bits(
                base_projection
            ),
        },
        "packed_word_program": {
            "word_bits": packed.word_bits,
            "groups": packed.group_count,
            "total_group_bits": packed.total_group_bits,
            "generator_events": packed.generator_events,
            "first_prime_gcd_calls": packed_first.gcd_calls,
            "first_prime_carry_ones": packed_first.carry_ones,
            "first_prime_index": packed_first.first_index,
            "broadword_groups": broadword.group_count,
            "broadword_packed_width_bits": broadword.packed_width_bits,
        },
        "self_modifying_wheel": {
            "limit": selfmod.limit,
            "generator_count": selfmod.generator_count,
            "groups": selfmod.group_count,
            "total_group_bits": selfmod.total_group_bits,
            "build_word_gcds": selfmod.build_gcd_calls,
        },
        "hyperbolic_packed_summary": {
            "count": hyperbolic.summary.count,
            "first": hyperbolic.summary.first,
            "generator_events": hyperbolic.generator_events,
            "active_factor_count": hyperbolic.active_factor_count,
            "cofactor_points": hyperbolic.cofactor_points,
            "roughness_word_gcds": hyperbolic.roughness_word_gcds,
            "first_hole_word_gcds": hyperbolic.first_hole_word_gcds,
            "packed_groups": hyperbolic.packed_groups,
            "total_group_bits": hyperbolic.total_group_bits,
        },
        "power_radix": power_radix,
        "zeckendorf": {
            "binary_nodes": binary.nonterminal_nodes,
            "binary_child_refs": 2 * binary.nonterminal_nodes,
            "fib_digits": fib.digits,
            "fib_nodes": fib.nonterminal_nodes,
            "fib_child_refs": fib.child_refs,
        },
        "factor_periods": {
            "base2": {
                "lanes": period2.lane_count,
                "signed_order_sum": period2.signed_order_sum,
                "signed_order_average": period2.signed_order_sum / period2.lane_count,
                "distinct_signed_orders": period2.distinct_signed_orders,
                "pisano_sum": period2.pisano_sum,
                "pisano_average": period2.pisano_sum / period2.lane_count,
                "distinct_pisano_periods": period2.distinct_pisano_periods,
            },
            "base64": {
                "lanes": period64.lane_count,
                "signed_order_sum": period64.signed_order_sum,
                "signed_order_average": period64.signed_order_sum / period64.lane_count,
                "distinct_signed_orders": period64.distinct_signed_orders,
            },
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Prime coordinate / pair-field experiment (v0.15.0)",
        "",
        "This experiment applies the reverse-and-add coordinate strategy to the prime projector: digit-pair addition, 0/1 carry fields, quotient-first set maps, packed integer programs, alternate radices, and Fibonacci/Zeckendorf coordinates.",
        "",
        "## Exact pair-addition theorem",
        "",
        "For `n = p + d` in radix `b`, let `S_i = p_i + d_i` and let `C_i` be the ordinary 0/1 carry field. Normalized digits satisfy",
        "",
        "```math",
        "z_i = S_i + C_i - b C_{i+1}.",
        "```",
        "",
        "But in the weighted integer sum the carry terms telescope, so",
        "",
        "```math",
        "n = \\sum_i S_i b^i.",
        "```",
        "",
        "Therefore every residue/divisibility projector can consume the unnormalised pair field directly. Keeping both pair sums and normalized prime digits would be duplicate state. The useful carry vector reappears below at the packed-wheel level, where it advances several bounded residues in parallel.",
        "",
        "## Least-factor tropical quotient",
        "",
        "Replace Boolean overlap by the winner field",
        "",
        "```math",
        "\\lambda(j)=\\min\\{q:q\\mid(start+2j)\\},",
        "```",
        "",
        "with `0`/infinity for a prime. A divisor lane survives only if it wins at least one candidate. This is an exact finite-window quotient.",
        "",
        "| candidates | periodic prime lanes | winning lanes | packed winning modulus bits | `(factor,phase)` bits |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row_1 in least_rows:
        lines.append(
            f"| {row_1['length']} | {row_1['periodic_lanes']} | {row_1['active_lanes']} | {row_1['active_modulus_bits']} | {row_1['periodic_factor_phase_bits']} |"
        )
    lines += [
        "",
        "At 4,096 candidates this removes 175 of 446 periodic prime lanes. Multiplying only the 271 winning factors gives a 2,515-bit window-specific modulus. The modulus is an exact canonical state for the projected block, but discovering it currently consumes the factor projection, so it is not charged as a free projector.",
        "",
        "## Prime-independent universal packed wheel",
        "",
        "Let `m=floor(sqrt(H))`. For every candidate `m < n <= H < (m+1)^2`,",
        "",
        "```math",
        "n \\text{ prime} \\iff \\gcd(n,\\operatorname{lcm}(1,\\ldots,m))=1.",
        "```",
        "",
        f"For this block `m={squarefree.limit}`. The raw LCM is {lcm.modulus_bits:,} bits. Canonicalizing repeated prime-power generators leaves a squarefree {squarefree.modulus_bits:,}-bit modulus discovered from all naturals with no supplied prime list. The previous 446 lane `(factor,phase)` coordinates alone cost {lane_min_description_bits(base_projection):,} bits.",
        "",
        "The squarefree generators can also be packed greedily into <=63-bit products. Their residues evolve as",
        "",
        "```math",
        "r_i' = r_i + 2 - M_i c_i, \\qquad c_i\\in\\{0,1\\}.",
        "```",
        "",
        f"That gives **{packed.group_count} packed lanes** instead of 446 factor lanes. Ordered small-factor-first, the search from 9,999,993 to 10,000,019 uses **{packed_first.gcd_calls} word-gcd probes** and an exact 0/1 wrap-carry vector. With <=62-bit groups those {broadword.group_count} residues fit in one **{broadword.packed_width_bits:,}-bit SWAR word**, and one +2 step computes every modular update/carry with a fixed broadword program.",
        "",
        "",
        "The generator carrier is also self-modifying: when extending the capacity from `m` to `m+1`, the existing packed groups classify the new integer itself. If it is coprime to every prior group, it is a new prime and is packed into the carrier; otherwise it is discarded. Building through 3,163 this way discovers the same 447 generators / 78 groups with **18,635 bounded-word gcds** and no parallel LCM state.",
        "",
        "## Hyperbolic rough-cofactor fusion",
        "",
        "Every composite has a unique least-factor decomposition",
        "",
        "```math",
        r"n=q r,\qquad q=\operatorname{spf}(n),\qquad \gcd(r,\prod_{p<q}p)=1.",
        "```",
        "",
        "For each newly discovered `q`, the possible `r` live only in the hyperbolic interval `[ceil(A/q), floor(B/q)]`. Testing those cofactors against the already-built packed prefix wheel makes the decomposition disjoint before any candidate bitmap exists.",
        "",
        f"For 4,096 candidates it examines **{hyperbolic.cofactor_points:,}** cofactor points and uses **{hyperbolic.roughness_word_gcds:,} bounded-word gcds**. Exactly {length - hyperbolic.summary.count:,} points survive as composites across **{hyperbolic.active_factor_count}** least-factor classes. The independent packed first-hole scan adds {hyperbolic.first_hole_word_gcds} gcd probes and returns the complete summary **({hyperbolic.summary.count}, {hyperbolic.summary.first})** without a block bitmap. The older floor-quotient implementation needs 1,716,105 sieve updates on this same block.",
        "",
        "## Power-of-two radix reinterpretations",
        "",
        "All rows below represent the same 4,096-candidate composite field and compile the finite winning lanes directly into an r-ary reduced DAG. Node identity alone is misleading, so child references and construction work are charged.",
        "",
        "| radix | digits | reachable nodes | reachable child refs | allocated nodes | allocated child refs | OR calls |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row_2 in power_radix:
        lines.append(
            f"| {row_2['radix']} | {row_2['digits']} | {row_2['reachable_nodes']} | {row_2['reachable_child_refs']} | {row_2['allocated_nodes']} | {row_2['allocated_child_refs']} | {row_2['or_calls']} |"
        )
    lines += [
        "",
        "Radix 8 looks dramatically smaller if only node IDs are counted (127 vs 456), but binary still has the smallest reachable child-reference payload (912) and the fewest OR calls. Radix 64 collapses to 65 high-arity nodes while retaining 4,160 outgoing references. This is exactly the late-accounting failure mode the main project is designed to reject.",
        "",
        "## Fibonacci / Zeckendorf coordinate",
        "",
        f"The 4,096 candidate indices require {fib.digits} Zeckendorf digits. The exact partial-domain decision DAG has **{fib.nonterminal_nodes} nodes / {fib.child_refs} child refs**, versus **{binary.nonterminal_nodes} / {2 * binary.nonterminal_nodes}** for ordinary binary. Factor divisibility also evolves with Pisano periods: across the 446 lanes the average Fibonacci period is **{period2.pisano_sum / period2.lane_count:.1f}**, versus an average signed power-of-two folding order of **{period2.signed_order_sum / period2.lane_count:.1f}** for base 2 and **{period64.signed_order_sum / period64.lane_count:.1f}** for base 64. Fibonacci does not expose a smaller modular carrier here.",
        "",
        "## Architectural conclusion",
        "",
        "The prime analogue of the reverse-and-add pair machinery is not to retain candidate normalization carries. Those carries telescope out of every modular test. The stronger state is:",
        "",
        "```text",
        "previous prime / offset",
        "    -> unnormalised pair-sum translation",
        "    -> packed squarefree factor modulus (or bounded word groups)",
        "    -> gcd zero-set",
        "    -> least-factor/min envelope",
        "    -> (count, first-hole) summary.",
        "```",
        "",
        "The new positive compression is the factor-set packing and finite least-factor quotient. The unresolved primitive is still first-hole/select over the coprime set without scanning candidates or unpacking the squarefree modulus. Different power-of-two and Fibonacci digit coordinates did not remove that projection barrier.",
        "",
        "Also, for odd primes the exact successor relation is `p_next = p + 2j` for the first admissible `j>0`; `2p+1` is a different (Sophie-Germain/safe-prime) construction and is not generally the next prime.",
    ]
    DOC.write_text("\n".join(lines) + "\n")
    print(json.dumps(metrics, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
