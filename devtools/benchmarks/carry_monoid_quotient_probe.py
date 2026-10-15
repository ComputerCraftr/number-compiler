"""v0.20 cross-family monoid/quotient search metrics."""

from __future__ import annotations

import json
from typing import TypedDict

from devtools.paths import report_directory, report_output, repository_root
from devtools.verification import exact_oracle
from devtools.verification.carry_action_quotient import analyze_carry_action_quotient
from devtools.verification.oracles.digit_power import (
    lucas_lehmer_digit_field,
    pepin_digit_field,
)
from devtools.verification.special_factor_reference import (
    fermat_factor_witness,
    mersenne_factor_witness,
)
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzSequenceSpec,
    FermatCompilation,
    FermatSequenceSpec,
    MersenneCompilation,
    MersenneSequenceSpec,
    PrimeBlockCompilation,
    PrimeBlockSequenceSpec,
    ReverseAddCompilation,
    ReverseAddSequenceSpec,
)
from number_compiler.arithmetic.fields.adic_morphism import (
    fermat_shifted_square_sensitivity,
    mersenne_successor_2adic_sensitivity,
    prime_translation_sensitivity,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    adaptive_square_convolution,
)
from number_compiler.sequences.prime.lane_quotient import (
    canonical_prime_base_period,
    compile_prime_block_lane_quotient,
)
from number_compiler.sequences.prime.radix_morphism_analysis import (
    mixed_radix_prime_residual_metrics,
    reinterpreted_prime_cyclotomic_metrics,
)

ROOT = repository_root()


class CompilationReport(TypedDict):
    reverse: ReverseAddCompilation
    prime: PrimeBlockCompilation
    fermat: FermatCompilation
    mersenne: MersenneCompilation


class PrimeScheduleRow(TypedDict):
    length: int
    old_period: list[int]
    new_period: list[int]
    old_projection_work: int
    new_projection_work: int
    work_ratio: float
    old_description_bits: int
    new_description_bits: int
    interfaces: int
    nodes: int
    prime_count: int
    first: int | None


@exact_oracle()
def main() -> None:
    prime_rows: list[PrimeScheduleRow] = []
    for length in (64, 256, 1024, 4096):
        old = compile_prime_block_lane_quotient(9_999_993, length, base_period=(4,))
        period = canonical_prime_base_period(length)
        new = compile_prime_block_lane_quotient(9_999_993, length, base_period=period)
        prime_rows.append(
            {
                "length": length,
                "old_period": [4],
                "new_period": list(period),
                "old_projection_work": old.projection_work,
                "new_projection_work": new.projection_work,
                "work_ratio": new.projection_work / old.projection_work,
                "old_description_bits": old.decision_description_bits,
                "new_description_bits": new.decision_description_bits,
                "interfaces": new.semantic_interfaces,
                "nodes": new.decision_nodes,
                "prime_count": new.summary_count,
                "first": new.summary_first,
            }
        )

    carry_rows = []
    for seed, base in ((196, 8), (196, 10), (195, 4)):
        m = analyze_carry_action_quotient(seed, base=base, transitions=512)
        carry_rows.append(
            {
                "seed": seed,
                "base": base,
                "actions": m.unique_nonlinear_actions,
                "reuses": m.nonlinear_action_reuses,
                "threshold_bits_average": m.threshold_bits_average,
                "reset_bits_average": m.reset_bits_average,
                "selected_bits_average": m.selected_signature_bits_average,
                "selected_bits_max": m.selected_signature_bits_max,
            }
        )

    collatz_rows = []
    compiler = CanonicalSequenceCompiler()
    for radix_1 in (2, 3, 6, 12, 18, 24, 30, 36):
        c = compiler.compile_diagnostic(CollatzSequenceSpec(27, radix_1, 111))
        collatz_rows.append(
            {
                "radix": radix_1,
                "steps": len(c.terms) - 1,
                "max_nodes": max(t.formula_nodes for t in c.terms),
                "max_description_bits": max(
                    t.formula_description_bits for t in c.terms
                ),
                "radial_key": list(c.normalized_padic_radial.canonical_key)
                if c.normalized_padic_radial is not None
                else None,
            }
        )

    special = []
    for family, result in (
        ("mersenne-31", lucas_lehmer_digit_field(31)),
        ("fermat-5", pepin_digit_field(5)),
    ):
        special.append(
            {
                "family": family,
                "iterations": result.iterations,
                "passes": result.passes,
                "scalar_products": result.karatsuba_scalar_multiplications,
                "coefficient_additions": result.coefficient_additions,
                "karatsuba_steps": result.karatsuba_steps,
                "schoolbook_steps": result.schoolbook_steps,
                "max_boundary_bits": result.max_boundary_bits,
            }
        )

    dense = []
    for width in (64, 128, 256, 512, 1024):
        _, metrics = adaptive_square_convolution((1,) * width)
        sb_m = width * width
        sb_a = sb_m - (2 * width - 1)
        dense.append(
            {
                "width": width,
                "algorithm": metrics.algorithm,
                "scalar_products": metrics.scalar_multiplications,
                "coefficient_additions": metrics.coefficient_additions,
                "charged_ops": metrics.scalar_multiplications
                + metrics.coefficient_additions,
                "schoolbook_charged_ops": sb_m + sb_a,
            }
        )

    factor_witnesses = []
    for family, parameter, factor, witness in (
        ("fermat", 5, 641, fermat_factor_witness(5, 641)),
        ("fermat", 5, 6700417, fermat_factor_witness(5, 6700417)),
        ("mersenne", 11, 23, mersenne_factor_witness(11, 23)),
        ("mersenne", 11, 89, mersenne_factor_witness(11, 89)),
    ):
        factor_witnesses.append(
            {
                "family": family,
                "parameter": parameter,
                "factor": factor,
                "compositions": witness.compositions,
                "divides": witness.divides,
                "stride_compatible": witness.stride_compatible,
            }
        )

    sensitivity = {
        "prime_2^20": {
            "key": list(
                prime_translation_sensitivity(2, 16).power(1 << 20).canonical_key
            ),
            "compositions": prime_translation_sensitivity(2, 16)
            .power(1 << 20)
            .compositions,
        },
        "fermat_index_12": {
            "key": list(fermat_shifted_square_sensitivity(64).power(12).canonical_key),
            "compositions": fermat_shifted_square_sensitivity(64)
            .power(12)
            .compositions,
        },
        "mersenne_exponent_8191": {
            "key": list(
                mersenne_successor_2adic_sensitivity(64).power(8190).canonical_key
            ),
            "compositions": mersenne_successor_2adic_sensitivity(64)
            .power(8190)
            .compositions,
        },
        "reverse_add_radial_example": {
            "key": list(
                power_two_cyclotomic_radial_quotient(4, 5, 12, bits=8).canonical_key
            ),
        },
    }

    reinterpret = []
    for radix_2 in (2, 3, 6, 10):
        cyclotomic_metrics = reinterpreted_prime_cyclotomic_metrics(
            9_999_993, 1024, radix_2
        )
        reinterpret.append(
            {
                "radix": radix_2,
                "classes": cyclotomic_metrics.classes,
                "ambiguous_classes": cyclotomic_metrics.ambiguous_classes,
                "ambiguous_candidates": cyclotomic_metrics.ambiguous_candidates,
                "modulus_bits": cyclotomic_metrics.modulus_bits,
            }
        )
    residual = []
    for period in ((2,), (4,), (4, 8), (4, 8, 16)):
        residual_metrics = mixed_radix_prime_residual_metrics(9_999_993, 1024, period)
        residual.append(
            {
                "period": list(period),
                "states": residual_metrics.residual_states_total,
                "max_states": residual_metrics.max_residual_states,
                "description_bits": residual_metrics.charged_description_bits,
                "references": residual_metrics.charged_references,
            }
        )

    # Verify the unified compiler actually retains the shared theorem paths.
    compiled: CompilationReport = {
        "reverse": compiler.compile_diagnostic(ReverseAddSequenceSpec(196, 10, 24)),
        "prime": compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, 4096)),
        "fermat": compiler.compile_diagnostic(FermatSequenceSpec((5,), test_through=5)),
        "mersenne": compiler.compile_diagnostic(
            MersenneSequenceSpec((31,), test_through=31)
        ),
    }
    assert compiled["prime"].translation_sensitivity is not None
    integration = {
        "reverse_radial_channels": len(compiled["reverse"].cyclotomic_radial_modes),
        "prime_period": list(compiled["prime"].decision.base_period),
        "prime_translation_compositions": compiled[
            "prime"
        ].translation_sensitivity.compositions,
        "fermat_digit_projection": compiled["fermat"].terms[0].digit_projection
        is not None,
        "mersenne_digit_projection": compiled["mersenne"].terms[0].digit_projection
        is not None,
    }

    data = {
        "prime_radix_schedule": prime_rows,
        "reverse_add_carry_automaton": carry_rows,
        "collatz_radix": collatz_rows,
        "special_digit_fields": special,
        "dense_square_crossover": dense,
        "special_factor_witnesses": factor_witnesses,
        "tropical_sensitivity": sensitivity,
        "prime_reinterpreted_cyclotomic": reinterpret,
        "prime_mixed_radix_residual": residual,
        "compiler_integration": integration,
    }
    outdir = report_directory("devtools.benchmarks.carry_monoid_quotient_probe")
    outdir.mkdir(exist_ok=True)
    out = outdir / "monoid_quotient_v020_metrics.json"
    out.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")

    md = [
        "# Cross-family monoid / quotient search — v0.20.0",
        "",
        "This pass charges construction and projection separately. A representation is retained only when it is an exact semantic quotient or when a static pre-execution optimizer selects it without compiling losing alternatives.",
        "",
        "## Prime residual-set radix schedule",
        "",
        "| candidates | v0.19 work | v0.20 period | v0.20 work | ratio | retained bits |",
        "|---:|---:|---|---:|---:|---:|",
    ]
    for r_1 in prime_rows:
        md.append(
            f"| {r_1['length']} | {r_1['old_projection_work']} | `{tuple(r_1['new_period'])}` | {r_1['new_projection_work']} | {r_1['work_ratio']:.3f} | {r_1['new_description_bits']} |"
        )
    md += [
        "",
        "The schedule is static: radix 4 below 1024 candidates and `(4,8)` at/above 1024. No rejected schedule is executed at runtime.",
        "",
        "## Reverse-add carry automaton",
        "",
        "The exact action key is now the carry-reset behavior. The compiler stores whichever exact encoding is cheaper: the palindromic half-threshold mask or the reset-change itinerary.",
        "",
        "| seed/base | unique actions | reuses | half-threshold avg bits | reset avg bits | selected avg bits |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for r_2 in carry_rows:
        md.append(
            f"| {r_2['seed']}/{r_2['base']} | {r_2['actions']} | {r_2['reuses']} | {r_2['threshold_bits_average']:.1f} | {r_2['reset_bits_average']:.1f} | {r_2['selected_bits_average']:.1f} |"
        )
    md += [
        "",
        "## Collatz operation-adapted radix",
        "",
        "| radix | max formula nodes | max description bits |",
        "|---:|---:|---:|",
    ]
    for r_3 in collatz_rows:
        md.append(
            f"| {r_3['radix']} | {r_3['max_nodes']} | {r_3['max_description_bits']} |"
        )
    md += [
        "",
        "Radix 6 remains the strongest tested single coordinate because multiplication by 3 and division by 2 are both local. Switching whole-number coordinates per branch was not retained because conversion is a separate linear digit projection.",
        "",
        "## Fermat/Mersenne digit-field carry quotient",
        "",
        "Every cyclic/negacyclic coefficient block normalizes through one scalar fixed/anti-fixed boundary carry; no carry vector is retained. The square compiler uses schoolbook on small/sparse fields and Karatsuba only after the charged crossover.",
        "",
        "| dense width | selected | charged ops | schoolbook charged ops |",
        "|---:|---|---:|---:|",
    ]
    for r_4 in dense:
        md.append(
            f"| {r_4['width']} | {r_4['algorithm']} | {r_4['charged_ops']} | {r_4['schoolbook_charged_ops']} |"
        )
    md += [
        "",
        "Supplied factor witnesses are even smaller: Fermat factor testing takes `n` modular squarings in the exponent-doubling coordinate, while Mersenne factor testing takes `O(log p)` binary modular compositions. Factor *search* remains separately unsolved/charged.",
        "",
        "## Prime bit reinterpretation",
        "",
        "Reinterpreting binary prime words into other radices exposes cyclotomic classes but does not classify the block: many classes remain mixed prime/composite. Mixed-radix residual languages do reduce finite automaton state, which is why the production projector uses a radix schedule on the factored congruence/set state rather than on raw prime bits.",
        "",
        "## Shared radial / sensitivity theorem stack",
        "",
        "The old reverse-add and Collatz valuation-only aliases are gone. Reverse-add now exposes the strictly richer exact radial split `2^q(1+z)^r = 2^v * unit`; Collatz exposes the exact p-adic affine map and its `PadicRadialQuotient`. The generic tropical `v -> min(W,a*v+b)` monoid remains only where valuation is the whole theorem channel (Fermat/Mersenne and prime controls). None of these derived views replaces exact sequence state.",
        "",
        "## Bound conclusion",
        "",
        "The new work reduces retained carry state and some projection constants/sublinear-looking finite-window work, and it gives logarithmic factor-witness/exponent morphisms for the special families. It does **not** prove logarithmic total primality projection, the Collatz conjecture, or a polylog decimal-196 full-J quotient. Those release blockers remain explicit.",
    ]
    (
        report_output(
            "devtools.benchmarks.carry_monoid_quotient_probe",
            "MONOID_QUOTIENT_V020_RESULTS.md",
        )
    ).write_text("\n".join(md) + "\n")
    print(out)
    print(
        report_output(
            "devtools.benchmarks.carry_monoid_quotient_probe",
            "MONOID_QUOTIENT_V020_RESULTS.md",
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
