"""Cross-domain radix/set/binomial compression probe for Collatz and primes."""

from __future__ import annotations

from devtools.benchmarks.reporting import write_json_report
from devtools.paths import report_directory, repository_root
from devtools.runs import run_reported
from number_compiler.arithmetic.fields.digit_formula import (
    synthesize_divide,
    synthesize_function_monoid,
    synthesize_multiply_add,
)
from number_compiler.projection.collatz_orbits.binary import collatz_orbit_formulas
from number_compiler.projection.radix_decision import (
    bitmap_radix_decision_metrics,
    collatz_inverse_symbolic_decision_metrics,
    shared_radix_decision_metrics,
)
from number_compiler.sequences.collatz.parity import (
    CollatzParityCursor,
    CollatzParityTimeOperator,
    collatz_parity_inverse_residue,
    collatz_parity_inverse_residue_binomial,
    collatz_parity_slab,
    collatz_parity_word,
    pow3_mod_pow2_binomial,
    valid_physical_branch_count,
)
from number_compiler.sequences.collatz.radix import collatz_orbit_formulas_ternary
from number_compiler.sequences.prime.binomial import project_binomial_prime_block
from number_compiler.sequences.prime.quotient import (
    prime_block_summary_quotient,
    prime_count_quotient,
)
from number_compiler.sequences.prime.radix import project_odd_prime_block_radix
from number_compiler.sequences.prime.set import project_odd_prime_block

ROOT = repository_root()


def radix_sweep() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for base in range(2, 17):
        mul = synthesize_function_monoid(synthesize_multiply_add(base, 3, 1))
        div = synthesize_function_monoid(synthesize_divide(base, 2))
        rows.append(
            {
                "base": base,
                "mul3_add1_transition_monoid": mul.size,
                "divide2_transition_monoid": div.size,
                "product_score": mul.size * div.size,
            }
        )
    return rows


def collatz_radix_metrics() -> dict[str, object]:
    _a2, binary = collatz_orbit_formulas(
        27, max_steps=111, stop_at_one=False, materialize_values=True
    )
    _a3, ternary = collatz_orbit_formulas_ternary(
        27, max_steps=111, stop_at_one=False, materialize_values=True
    )
    points: list[dict[str, object]] = []
    for step in (1, 8, 16, 32, 64, 96, 111):
        b = binary[step]
        t = ternary[step]
        points.append(
            {
                "step": step,
                "binary_formula_nodes": b.formula_nodes,
                "ternary_formula_nodes": t.formula_nodes,
                "ternary_over_binary": t.formula_nodes / b.formula_nodes,
                "binary_width": b.width,
                "ternary_width": t.width,
            }
        )
    return {"base_sweep": radix_sweep(), "seed_27": points}


def collatz_parity_metrics() -> dict[str, object]:
    maps: list[dict[str, object]] = []
    # Keep a truth-table differential through width 12, then switch to the exact
    # residual-state construction.  This removes the old 2**k materialization
    # from the benchmark while preserving an independent check of the symbolic
    # path at bounded width.
    for width in (4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30):
        symbolic = collatz_inverse_symbolic_decision_metrics(width)
        if width <= 12:
            outputs = tuple(
                collatz_parity_inverse_residue(word, width)
                for word in range(1 << width)
            )
            ordinary = shared_radix_decision_metrics(outputs, width, width, order="lsb")
            assert ordinary.nonterminal_nodes == symbolic.nonterminal_nodes
        maps.append(
            {
                "width": width,
                "residue_classes": 1 << width,
                "shared_radix_nodes": symbolic.nonterminal_nodes,
                "symbolic_residual_states": symbolic.symbolic_states,
                "residual_state_upper_bound": symbolic.residual_state_upper_bound,
                "classes_per_node": (1 << width) / symbolic.nonterminal_nodes,
            }
        )

    native_slabs: list[dict[str, object]] = []
    for width in (8, 16, 32, 64, 128, 256, 512, 1024, 2048):
        word = collatz_parity_word(27, width)
        slab = collatz_parity_slab(word, width)
        assert slab.domain_residue == 27 % (1 << width)
        native_slabs.append(
            {
                "width": width,
                "ones": slab.ones,
                "offset_bits": max(1, slab.offset.bit_length()),
                "description_bits": slab.description_bits,
                "balanced_composition_depth_upper_bound": (width - 1).bit_length(),
            }
        )

    powered: list[dict[str, object]] = []
    for steps in (8, 16, 32, 64, 128, 256, 512, 1024):
        width = steps + 2
        word = collatz_parity_word(27, width)
        op = CollatzParityTimeOperator(steps)
        advanced = op.apply(CollatzParityCursor(word, width))
        powered.append(
            {
                "physical_steps": steps,
                "explicit_legal_branch_words_bit_length": valid_physical_branch_count(
                    steps
                ).bit_length(),
                "operator_nodes": op.operator_nodes,
                "operator_description_bits": op.description_bits,
                "consumed_parity_symbols": advanced.consumed_symbols,
                "result_phase": advanced.cursor.phase,
                "rank_queries": advanced.rank_queries,
                "bigint_rank_bits_scanned": advanced.rank_bits_scanned,
            }
        )

    binomial: list[dict[str, object]] = []
    for exponent in (1, 5, 17, 257, 1 << 20):
        bits = 5
        modulus = 1 << bits
        positive = pow3_mod_pow2_binomial(exponent, bits)
        inverse = pow3_mod_pow2_binomial(exponent, bits, inverse=True)
        assert positive == pow(3, exponent, modulus)
        assert inverse == pow(positive, -1, modulus)
        binomial.append(
            {
                "exponent": exponent,
                "bits": bits,
                "three_power_mod": positive,
                "inverse_three_power_mod": inverse,
                "max_binomial_terms": bits,
            }
        )

    # Independent set-map/binomial path differential on every 12-bit parity word.
    for word in range(1 << 12):
        assert collatz_parity_inverse_residue_binomial(
            word, 12
        ) == collatz_parity_inverse_residue(word, 12)

    return {
        "inverse_parity_radix_dag": maps,
        "native_parity_slabs": native_slabs,
        "physical_powered_shift": powered,
        "fixed_width_binomial_three_powers": binomial,
    }


def prime_metrics() -> dict[str, object]:
    p = 9_999_991
    start = p + 2
    radix_rows: list[dict[str, object]] = []
    for length_1 in (16, 32, 64, 128, 256, 512, 1024, 2048, 4096):
        ordinary = project_odd_prime_block(start, length_1)
        radix = project_odd_prime_block_radix(start, length_1)
        bitmap_bdd = bitmap_radix_decision_metrics(
            ordinary.composite_mask, length_1.bit_length() - 1, order="msb"
        )
        assert radix.summary == ordinary.summary
        assert radix.reachable_bdd_nodes == bitmap_bdd.nonterminal_nodes
        radix_rows.append(
            {
                "candidates": length_1,
                "natural_factor_lanes": ordinary.natural_lanes,
                "canonical_factor_lanes": len(ordinary.canonical_lanes),
                "reachable_radix_bdd_nodes": radix.reachable_bdd_nodes,
                "allocated_radix_bdd_nodes": radix.allocated_bdd_nodes,
                "bdd_or_calls": radix.or_calls,
            }
        )

    pascal_rows: list[dict[str, object]] = []
    for length_2 in (16, 64, 256):
        projection = project_binomial_prime_block(9_993, length_2)
        multiplicative = project_odd_prime_block(9_993, length_2)
        assert projection.composite_mask == multiplicative.composite_mask
        pascal_rows.append(
            {
                "candidates": length_2,
                "active_binomial_witness_lanes": projection.natural_witness_lanes,
                "canonical_binomial_lanes": len(projection.canonical_lanes),
                "canonical_k": [lane.k for lane in projection.canonical_lanes],
            }
        )

    quotient_scale: list[dict[str, object]] = []
    for n in (10_000, 1_000_000, 10_000_000, 100_000_000):
        result = prime_count_quotient(n)
        quotient_scale.append(
            {
                "n": n,
                "pi_n": result.count,
                "quotient_states": result.quotient_states,
                "sieve_updates": result.sieve_updates,
                "discovered_primes": result.discovered_primes,
            }
        )

    quotient_blocks: list[dict[str, object]] = []
    for length_3 in (16, 64, 256, 1024, 4096):
        block_result = prime_block_summary_quotient(start, length_3)
        ordinary = project_odd_prime_block(start, length_3)
        assert block_result.summary == ordinary.summary
        quotient_blocks.append(
            {
                "candidates": length_3,
                "prime_count": block_result.summary.count,
                "first_prime_index": block_result.summary.first,
                "pi_queries": block_result.pi_queries,
                "max_quotient_states": block_result.max_quotient_states,
                "total_sieve_updates": block_result.total_sieve_updates,
            }
        )

    return {
        "direct_radix_projection": radix_rows,
        "pascal_binomial_projection": pascal_rows,
        "hyperbolic_quotient_scale": quotient_scale,
        "hyperbolic_block_summary": quotient_blocks,
    }


def main() -> None:
    data = {
        "collatz_radix": collatz_radix_metrics(),
        "collatz_parity": collatz_parity_metrics(),
        "prime": prime_metrics(),
        "conclusions": {
            "collatz": (
                "The unaccelerated map is an exact two-phase suspension of the parity shift. "
                "Physical T^N becomes weighted rank/select plus a shift; coordinate conversion remains the hard projection."
            ),
            "prime_binomial": (
                "Pascal translation is exactly (I+S)^h, but quotienting witness lanes returns prime-divisor lanes."
            ),
            "prime_radix": (
                "The final radix BDD is compact, but intermediate construction work exceeds the irreducible lane basis."
            ),
            "prime_hyperbola": (
                "Floor-quotient state computes count/first without a bitmap and is stable in block length, but grows as sqrt(n), not polylog(n)."
            ),
        },
    }
    out = (
        report_directory("devtools.benchmarks.radix_set_binomial_probe")
        / "radix_set_binomial_metrics.json"
    )
    write_json_report(out, data)


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
