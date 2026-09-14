"""Cyclotomic / Fermat / Mersenne / binary-prime automaton probe for v0.17."""

from __future__ import annotations

import json
from math import isqrt, sqrt

from devtools.benchmarks.report_schema import record, records
from devtools.paths import report_output, repository_root
from devtools.proofs.oracles.special_primality import lucas_lehmer_test, pepin_test
from number_compiler.arithmetic.carry.carry_itinerary import (
    adaptive_negacyclic_memory_horizon,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.polynomials.cyclotomic import (
    cyclotomic_one_plus_norm,
    cyclotomic_two_adic_growth_channel,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_modulus,
    power_two_cyclotomic_transport,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.projection.radix_decision import (
    collatz_inverse_symbolic_decision_metrics,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
    fermat_factor_stride,
    fermat_number,
    fermat_previous_product,
    mersenne_composite_exponent_factor,
    mersenne_factor_stride,
    mersenne_gcd_spec,
    mersenne_number,
)
from number_compiler.sequences.prime.automaton import (
    boolean_anf_metrics,
    boolean_coordinate_derivative_metrics,
    prime_cyclotomic_order_metrics,
    prime_lsb_residual_kernel,
)
from number_compiler.sequences.prime.set import project_odd_prime_block

ROOT = repository_root()

OUT = ROOT / "results" / "cyclotomic_special_metrics.json"
REPORT = report_output(
    "devtools.benchmarks.cyclotomic_special_probe", "CYCLOTOMIC_SPECIAL_RESULTS.md"
)


def pair_from_int(value: int, base: int = 10) -> tuple[int, ...]:
    digits: list[int] = []
    n = int(value)
    while n:
        digits.append(n % base)
        n //= base
    digits = digits or [0]
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def reverse_growth_trace(steps: int = 512) -> list[int]:
    pair = pair_from_int(196)
    growths: list[int] = []
    for _ in range(steps + 32):
        pair, growth = pair_step(pair, 10)
        growths.append(growth)
    return growths


def reverse_cyclotomic_metrics() -> dict[str, object]:
    growths = reverse_growth_trace(512)
    rows = []
    for classes in (1, 2, 4, 8, 16):
        horizons = []
        for endpoint in range(32, 513):
            horizon = adaptive_negacyclic_memory_horizon(
                growths, endpoint, classes=classes, bits=5
            )
            if horizon is None:
                raise AssertionError((classes, endpoint))
            horizons.append(horizon)
        transport = power_two_cyclotomic_transport(classes, 0, classes)
        fermat_index = classes.bit_length() - 1
        assert power_two_cyclotomic_modulus(2, classes) == fermat_number(fermat_index)
        rows.append(
            {
                "classes": classes,
                "cyclotomic_order": 2 * classes,
                "decimal_digit_modulus": power_two_cyclotomic_modulus(10, classes),
                "binary_digit_modulus": power_two_cyclotomic_modulus(2, classes),
                "fermat_index_at_radix_2": fermat_index,
                "growth_block_scalar_v2": transport.scalar_v2,
                "growth_block_exact_zero": transport.exact_zero,
                "average_dependency_horizon": sum(horizons) / len(horizons),
                "max_dependency_horizon": max(horizons),
            }
        )

    norm_rows = []
    for order in (1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 18, 20, 32):
        norm_rows.append(
            {
                "order": order,
                "abs_Phi_n_minus1": cyclotomic_one_plus_norm(order),
                "two_adic_growth_class": cyclotomic_two_adic_growth_channel(order),
            }
        )
    return {
        "power_two_channels": rows,
        "one_plus_z_norms": norm_rows,
        "closed_rule": "v2(content(2^q(1+z)^r mod Phi_(2m))) = q + floor(r/m), m>=2 power-of-two",
    }


def collatz_inverse_metrics() -> dict[str, object]:
    rows = []
    for width in (12, 16, 20, 22, 24, 26, 28, 30, 32):
        metrics = collatz_inverse_symbolic_decision_metrics(width)
        scale = sqrt(width) * (2 ** (width / 2))
        rows.append(
            {
                "width": width,
                "truth_table_rows_avoided": 1 << width,
                "shared_nodes": metrics.nonterminal_nodes,
                "symbolic_states": metrics.symbolic_states,
                "residual_state_upper_bound": metrics.residual_state_upper_bound,
                "nodes_over_sqrt_k_2_pow_k_over_2": metrics.nonterminal_nodes / scale,
                "nodes_over_k_2_pow_k_over_2": metrics.nonterminal_nodes
                / (width * (2 ** (width / 2))),
            }
        )
    return {
        "symbolic_inverse_parity_dag": rows,
        "frontier_bound": "min(2^l,(l+1)2^(t+1-l))",
        "derived_asymptotic_upper_bound": "O(sqrt(k) 2^(k/2))",
    }


def _fermat_square_field_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for index in range(2, 7):
        spec = FermatNumberSpec(index)
        modulus = spec.materialize()
        value = 3 % modulus
        alphabet: set[int] = set()
        fields: set[tuple[int, ...]] = set()
        nonzero = []
        low = high = 0
        for _ in range(spec.exponent - 1):
            projection = negacyclic_binary_square_projection(value, spec.exponent)
            field = projection.field
            fields.add(field)
            alphabet.update(field)
            low = min(low, min(field))
            high = max(high, max(field))
            nonzero.append(sum(x != 0 for x in field))
            assert projection.residue == value * value % modulus
            value = projection.residue
        rows.append(
            {
                "index": index,
                "cyclotomic_order": spec.cyclotomic_order,
                "digit_width": spec.exponent,
                "squarings": spec.exponent - 1,
                "distinct_raw_square_fields": len(fields),
                "coefficient_min": low,
                "coefficient_max": high,
                "coefficient_alphabet": len(alphabet),
                "average_nonzero_coefficients": sum(nonzero) / len(nonzero),
                "pepin_pass": value == modulus - 1,
            }
        )
    return rows


def _mersenne_square_field_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for exponent in (7, 11, 13, 19, 23, 31):
        modulus = mersenne_number(exponent)
        value = 4 % modulus
        alphabet: set[int] = set()
        fields: set[tuple[int, ...]] = set()
        nonzero = []
        high = 0
        for _ in range(max(0, exponent - 2)):
            projection = cyclic_binary_square_projection(value, exponent)
            field = projection.field
            fields.add(field)
            alphabet.update(field)
            high = max(high, max(field))
            nonzero.append(sum(x != 0 for x in field))
            assert projection.residue == value * value % modulus
            value = (projection.residue - 2) % modulus
        ll = lucas_lehmer_test(exponent)
        assert value == ll.residue
        rows.append(
            {
                "exponent": exponent,
                "cyclotomic_order_if_prime_exponent": exponent,
                "iterations": ll.iterations,
                "distinct_raw_square_fields": len(fields),
                "coefficient_max": high,
                "coefficient_alphabet": len(alphabet),
                "average_nonzero_coefficients": sum(nonzero) / len(nonzero)
                if nonzero
                else 0,
                "lucas_lehmer_pass": ll.passes,
                "single_trace_residue": ll.residue,
            }
        )
    return rows


def special_number_metrics() -> dict[str, object]:
    fermat = []
    for index in range(7):
        spec = FermatNumberSpec(index)
        row = {
            "index": index,
            "cyclotomic_order": spec.cyclotomic_order,
            "bit_length": spec.bit_length,
            "symbolic_description_bits": spec.description_bits,
            "previous_product_identity": fermat_previous_product(index)
            == spec.materialize() - 2,
        }
        if index >= 1:
            pepin = pepin_test(index)
            row.update(
                {
                    "pepin_squarings": pepin.squarings,
                    "pepin_pass": pepin.passes,
                }
            )
        fermat.append(row)

    f5 = fermat_number(5)
    f_stride = fermat_factor_stride(5)
    fermat_factor_window = {
        "index": 5,
        "sqrt_F": isqrt(f5),
        "forced_stride": f_stride,
        "congruence_candidates_to_sqrt": (isqrt(f5) - 1) // f_stride,
        "known_factors_checked": [
            {"factor": q, "residue": q % f_stride} for q in (641, 6_700_417)
        ],
    }

    mersenne = []
    for exponent in (3, 5, 7, 11, 13, 17, 19, 23, 31):
        mersenne_spec = MersenneNumberSpec(exponent)
        ll = lucas_lehmer_test(exponent)
        divisor = mersenne_composite_exponent_factor(exponent)
        mersenne.append(
            {
                "exponent": exponent,
                "bit_length": mersenne_spec.bit_length,
                "symbolic_description_bits": mersenne_spec.description_bits,
                "exponent_has_symbolic_mersenne_divisor": divisor.exponent
                if divisor
                else None,
                "lucas_lehmer_iterations": ll.iterations,
                "lucas_lehmer_pass": ll.passes,
                "single_trace_residue": ll.residue,
            }
        )

    gcd_examples = []
    for a, b in ((12, 18), (15, 25), (31, 62)):
        g = mersenne_gcd_spec(a, b)
        gcd_examples.append({"a": a, "b": b, "gcd_exponent": g.exponent})

    m23 = mersenne_number(23)
    m_stride = mersenne_factor_stride(23)
    mersenne_factor_window = {
        "exponent": 23,
        "sqrt_M": isqrt(m23),
        "forced_stride": m_stride,
        "congruence_candidates_to_sqrt": (isqrt(m23) - 1) // m_stride,
        "known_factor": 47,
        "known_factor_residue": 47 % m_stride,
    }

    return {
        "fermat_generation_and_pepin": fermat,
        "fermat_negacyclic_square_fields": _fermat_square_field_rows(),
        "fermat_factor_hyperbolic_restriction": fermat_factor_window,
        "mersenne_generation_and_lucas_lehmer": mersenne,
        "mersenne_cyclic_square_fields": _mersenne_square_field_rows(),
        "mersenne_gcd_exponent_lattice": gcd_examples,
        "mersenne_factor_hyperbolic_restriction": mersenne_factor_window,
    }


def prime_automaton_metrics() -> dict[str, object]:
    residuals = []
    for prefix_bits in range(1, 11):
        metrics = prime_lsb_residual_kernel(prefix_bits, 8)
        residuals.append(
            {
                "prefix_bits": prefix_bits,
                "tail_bits": 8,
                "odd_prefixes": metrics.odd_prefixes,
                "distinct_residuals": metrics.distinct_residuals,
                "merge_fraction": 1 - metrics.distinct_residuals / metrics.odd_prefixes,
                "sieve_limit": metrics.sieve_limit,
                "sieve_updates": metrics.sieve_updates,
            }
        )

    anf = []
    start = 9_999_993
    for length in (64, 128, 256, 512, 1024, 2048, 4096):
        projection = project_odd_prime_block(start, length)
        boolean_metrics = boolean_anf_metrics(
            projection.prime_mask, length.bit_length() - 1
        )
        anf.append(
            {
                "candidates": length,
                "input_bits": boolean_metrics.input_bits,
                "anf_degree": boolean_metrics.degree,
                "anf_terms": boolean_metrics.terms,
                "terms_by_degree": list(boolean_metrics.terms_by_degree),
            }
        )
    block = project_odd_prime_block(start, 4096)
    derivative = boolean_coordinate_derivative_metrics(block.prime_mask, 12)
    cyclotomic = prime_cyclotomic_order_metrics(3163)
    return {
        "lsb_two_kernel_residuals": residuals,
        "odd_block_boolean_anf": anf,
        "coordinate_derivatives_4096": {
            "constant_derivatives": derivative.constant_derivatives,
            "ones": list(derivative.derivative_ones),
            "pairs": list(derivative.pair_counts),
            "densities": list(derivative.densities),
        },
        "binary_cyclotomic_wheel_orders": {
            "limit": cyclotomic.limit,
            "generators": cyclotomic.generators,
            "odd_generators": cyclotomic.odd_generators,
            "exact_order_groups": cyclotomic.exact_order_groups,
            "signed_order_groups": cyclotomic.signed_order_groups,
            "max_exact_group_size": cyclotomic.max_exact_group_size,
            "max_signed_group_size": cyclotomic.max_signed_group_size,
        },
        "interpretation": (
            "The set-to-set maps n->2n+r produce distinct bounded residual prime languages for every "
            "odd r tested. Direct binary automaticity and affine coordinate structure do not collapse; "
            "binary cyclotomic-order grouping also barely merges the wheel generators. The packed wheel remains the useful quotient."
        ),
    }


def write_report(data: dict[str, dict[str, object]]) -> None:
    cyc = data["reverse_add_cyclotomic"]
    coll = data["collatz_inverse"]
    _special = data["special_numbers"]
    prime = data["prime_automaton"]
    lines = [
        "# Cyclotomic / Fermat / Mersenne / binary-prime results — v0.17.0",
        "",
        "This pass asks whether the digit fields already used by reverse-add, Collatz, and the prime projector hide a stronger cyclotomic or automatic quotient. The new objects remain derived compiler/research interfaces; they do not replace the canonical reverse-add state.",
        "",
        "## 1. Reverse-add cyclotomic theorem",
        "",
        "For power-of-two `m`, `z^m+1 = Phi_(2m)(z)`. For `m>=2`, `(1+z)^m = 2 U_m(z)` in that quotient and `U_m` is a 2-adic unit. Therefore the exact coefficient-content valuation is `q + floor(r/m)` for `2^q(1+z)^r`. The earlier negacyclic kernel expansion is retained as the independent differential path, while the production annihilation query now consumes the closed valuation theorem.",
        "",
        "| m | cyclotomic order | decimal modulus | Fermat index at radix 2 | avg horizon | max horizon |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row_1 in records(cyc["power_two_channels"]):
        lines.append(
            f"| {row_1['classes']} | {row_1['cyclotomic_order']} | {row_1['decimal_digit_modulus']} | "
            f"{row_1['fermat_index_at_radix_2']} | {row_1['average_dependency_horizon']:.3f} | {row_1['max_dependency_horizon']} |"
        )
    lines += [
        "",
        "The norm classification also explains why this family is special: `abs(Phi_n(-1))` is even only on the 2-power cyclotomic orders (apart from the exact `Phi_2` zero channel). Odd Mersenne-like cyclotomic orders make `1+z` a 2-adic unit, so growth cannot erase them by itself.",
        "",
        "## 2. The Collatz k*2^(k/2) observation becomes a symbolic construction",
        "",
        "For output bit `t`, after assigning `l` low parity bits the residual `Q_k^-1` function is determined by only `(prefix popcount, truncated affine residue)`. Its exact frontier is bounded by `min(2^l,(l+1)2^(t+1-l))`. Splitting at the meet-in-the-middle point gives an `O(sqrt(k) 2^(k/2))` upper bound for the whole shared LSB decision construction. This is stronger than the earlier empirical `k*2^(k/2)` fit and avoids the `2^k` truth table entirely.",
        "",
        "| k | avoided truth rows | shared nodes | symbolic states | finite state bound |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row_2 in records(coll["symbolic_inverse_parity_dag"]):
        lines.append(
            f"| {row_2['width']} | {row_2['truth_table_rows_avoided']:,} | {row_2['shared_nodes']:,} | "
            f"{row_2['symbolic_states']:,} | {row_2['residual_state_upper_bound']:,} |"
        )
    lines += [
        "",
        "## 3. Fermat and Mersenne are native cyclotomic stress tests",
        "",
        "`F_n = Phi_(2^(n+1))(2)` is exactly the radix-2 evaluation of the same power-of-two negacyclic family. Subtracting one gives the pure squaring coordinate `F_n-1=2^(2^n)`, so generation is exponent doubling. Pepin primality remains a projection requiring `2^n-1` modular squarings.",
        "",
        "For prime exponent `p`, `M_p = Phi_p(2)`. Composite exponents are rejected before any Lucas-Lehmer work because `M_d | M_n` whenever `d|n`; more generally `gcd(M_a,M_b)=M_gcd(a,b)`. Lucas-Lehmer's nonlinear recurrence `s->s^2-2` has the quadratic-unit conjugacy `s_j = alpha^(2^j)+alpha^(-2^j)` with `alpha=2+sqrt(3)`, so its time operator is again exponent doubling while modular projection remains charged.",
        "",
        "The raw multiplication digit fields expose the expected cyclotomic convolution: Mersenne squaring is cyclic autocorrelation modulo `z^p-1`; Fermat squaring is negacyclic autocorrelation modulo `z^(2^n)+1 = Phi_(2^(n+1))(z)`. These fields are exact, but the measured raw rows are nearly all distinct, so they are testbeds/conjugacies rather than a newly compressed primality state.",
        "",
        "Fermat factor lanes also inherit a strong hyperbolic restriction: for `F_5`, only 511 numbers of the form `1 mod 128` lie below `sqrt(F_5)`, and both known factors satisfy it. Mersenne factors analogously lie in `1 mod 2p`.",
        "",
        "## 4. Direct binary prime automata do not collapse",
        "",
        "The natural base-2 set morphisms are the 2-kernel maps `P(n) -> P(2^e n+r)`. A finite LSB-first automaton would have to merge many odd residue prefixes. On an exact 256-sample residual vector (`tail_bits=8`), every odd prefix through ten bits has a distinct residual prime vector:",
        "",
        "| prefix bits | odd prefixes | distinct residuals |",
        "|---:|---:|---:|",
    ]
    for row_3 in records(prime["lsb_two_kernel_residuals"]):
        lines.append(
            f"| {row_3['prefix_bits']} | {row_3['odd_prefixes']} | {row_3['distinct_residuals']} |"
        )
    lines += [
        "",
        "The finite odd-prime block also rejects an affine Boolean model: at 4096 candidates the algebraic normal form has full degree 12 with 2,060 monomials, and none of its 12 coordinate derivatives is constant (their disagreement densities lie between 22.02% and 23.29%).",
        "",
        f"Cyclotomic grouping does not rescue the raw binary wheel either: the {record(prime['binary_cyclotomic_wheel_orders'])['odd_generators']} odd generators through 3163 occupy {record(prime['binary_cyclotomic_wheel_orders'])['exact_order_groups']} exact `ord_q(2)` channels, or {record(prime['binary_cyclotomic_wheel_orders'])['signed_order_groups']} channels after identifying +/- periods. That is far worse than the existing 78 bounded-word packed groups.",
        "",
        "Binary remains the best *implementation radix* found for the factor/wheel projector, but the raw prime Boolean vector does not reveal a small universal automaton. The useful automaton is still the factored packed wheel, whose state is the product of small congruence automata rather than prime bits themselves.",
        "",
        "## 5. Architectural consequence",
        "",
        "The reusable pattern is now clearer: use cyclotomic decomposition to identify nilpotent/ramified theorem channels, use coordinate conjugacies to power time (Collatz parity shift, Fermat squaring, Lucas-Lehmer quadratic-unit doubling), and keep primality/event projection separately charged. No result here proves a polylog temporal successor quotient for the current finite 196 defect-domain morphism.",
        "",
    ]
    REPORT.write_text("\n".join(lines))


def main() -> None:
    data = {
        "reverse_add_cyclotomic": reverse_cyclotomic_metrics(),
        "collatz_inverse": collatz_inverse_metrics(),
        "special_numbers": special_number_metrics(),
        "prime_automaton": prime_automaton_metrics(),
    }
    OUT.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    write_report(data)
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
