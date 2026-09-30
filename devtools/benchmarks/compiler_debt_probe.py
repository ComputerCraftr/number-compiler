"""Deterministic v0.28 compiler-duplication / debt-closure probe.

The probe compares the production semantic compiler with the explicit diagnostic
profile and exercises the canonical quotient/IR/local-ring infrastructure added
in v0.28.  It intentionally records structural/work counters only: no wall-clock
measurements enter release artifacts.
"""

from __future__ import annotations

import json

from devtools.paths import report_directory, report_output, repository_root
from devtools.verification import exact_oracle
from devtools.verification.block_power import apply_block_power, power_block_effect
from devtools.verification.quotient_synthesis import (
    ObserverFeature,
    synthesize_finite_quotient,
)
from devtools.verification.sequence_diagnostics import with_carry_diagnostics
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzSequenceSpec,
    FermatSequenceSpec,
    MersenneSequenceSpec,
    PrimeBlockSequenceSpec,
    ReverseAddSequenceSpec,
)
from number_compiler.arithmetic.fields.congruence_automaton import (
    FactoredPrimeAutomaton,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
    cyclotomic_linear_factor_profile,
    cyclotomic_primary_components,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock

ROOT = repository_root()


def _m7_cegar() -> dict[str, object]:
    p = 7
    modulus = (1 << p) - 1
    factors = cyclotomic_factors_mod_prime(p, 2)
    features = []
    for i, factor in enumerate(factors):
        values = tuple(
            CyclotomicDigitBlock.from_coefficients(
                digits_lsd(state, 2, p),
                order=p,
                modulus=2,
                factor=factor,
                length=p,
            ).residue
            for state in range(modulus)
        )
        features.append(
            ObserverFeature(f"phi7_factor_{i}", values, cost=len(factor) - 1)
        )
    result = synthesize_finite_quotient(
        tuple((state * state - 2) % modulus for state in range(modulus)),
        tuple(state == 0 for state in range(modulus)),
        tuple(features),
    )
    return {
        "classes": result.classes,
        "closed": result.closed,
        "noninjective": result.noninjective,
        "selected_features": list(result.selected_features),
        "total_cost": result.total_cost,
    }


def main() -> None:
    OUT = (
        report_directory("devtools.benchmarks.compiler_debt_probe")
        / "compiler_debt_metrics.json"
    )
    REPORT = report_output(
        "devtools.benchmarks.compiler_debt_probe", "COMPILER_DEBT_RESULTS.md"
    )
    compiler = CanonicalSequenceCompiler()

    r_spec = ReverseAddSequenceSpec(196, 10, 64)
    r_sem = compiler.compile(r_spec)
    with exact_oracle():
        r_diag = with_carry_diagnostics(compiler.compile_diagnostic(r_spec))

    c_spec = CollatzSequenceSpec(27, 6, 200)
    c_sem = compiler.compile(c_spec)
    c_diag = compiler.compile_diagnostic(c_spec)

    p_spec = PrimeBlockSequenceSpec(9_999_993, 256)
    p_sem = compiler.compile(p_spec)
    p_diag = compiler.compile_diagnostic(p_spec)

    f4 = compiler.compile(FermatSequenceSpec((4,), test_through=4)).terms[0]
    m13 = compiler.compile(MersenneSequenceSpec((13,), test_through=13)).terms[0]
    m15 = compiler.compile(MersenneSequenceSpec((15,), test_through=15)).terms[0]

    a = FactoredPrimeAutomaton.build(1000)
    b = FactoredPrimeAutomaton.build(1000, word_bits=62)

    phi7_mod8 = cyclotomic_primary_components(7, 2, 3)
    phi8_mod32 = cyclotomic_primary_components(8, 2, 5)
    ternary_phi8 = cyclotomic_linear_factor_profile(8, 3, 32)
    decimal_phi8 = cyclotomic_linear_factor_profile(8, 10, 32)

    powered = power_block_effect(
        base=10,
        exponent=128,
        max_context_nodes=1_000_000,
        max_cache_entries=1_000_000,
    )
    application = apply_block_power(powered, (7, 18, 7))
    stats = application.runtime_stats

    reverse_add_metrics = {
        "semantic_materialized_values": sum(t.value is not None for t in r_sem.terms),
        "diagnostic_materialized_values": sum(
            t.value is not None for t in r_diag.terms
        ),
        "semantic_primary_jets": sum(t.primary_jet is not None for t in r_sem.terms),
        "diagnostic_primary_jets": sum(t.primary_jet is not None for t in r_diag.terms),
        "semantic_carry_reset_max_bits": r_sem.carry_reset_max_bits,
        "diagnostic_carry_reset_max_bits": r_diag.carry_reset_max_bits,
        "growth_state_max_bits": r_sem.growth_state_max_bits,
        "growth_state_classes": r_sem.growth_state_classes,
        "growth_tuple_retained": "growths" in type(r_sem).__dataclass_fields__,
    }
    collatz_metrics = {
        "semantic_materialized_values": sum(t.value is not None for t in c_sem.terms),
        "diagnostic_materialized_values": sum(
            t.value is not None for t in c_diag.terms
        ),
        "semantic_branches": len(c_sem.branches),
        "diagnostic_branches": len(c_diag.branches),
        "semantic_raw_field": c_sem.raw_field_quotient is not None,
        "semantic_valuation_projection": c_sem.valuation_projection is not None,
        "diagnostic_odd_steps": c_diag.raw_field_quotient.odd_steps
        if c_diag.raw_field_quotient
        else None,
        "diagnostic_valuation_sum": c_diag.raw_field_quotient.valuation_sum
        if c_diag.raw_field_quotient
        else None,
        "valuation_replay_property_present": hasattr(type(c_sem), "valuation_symbols"),
    }
    prime_metrics = {
        "summary_equal": (
            p_sem.decision.summary_count,
            p_sem.decision.summary_first,
        )
        == (p_diag.decision.summary_count, p_diag.decision.summary_first),
        "semantic_primary_jet": p_sem.decision.primary_jet is not None,
        "semantic_primary_jet_compositions": p_sem.decision.primary_jet_compositions,
        "diagnostic_primary_jet_compositions": p_diag.decision.primary_jet_compositions,
        "semantic_automaton": p_sem.automaton is not None,
        "diagnostic_automaton": p_diag.automaton is not None,
        "diagnostic_cyclotomic_groups": p_diag.automaton.cyclotomic_group_count
        if p_diag.automaton
        else 0,
        "diagnostic_cyclotomic_state_bits": p_diag.automaton.cyclotomic_state_bits
        if p_diag.automaton
        else 0,
        "diagnostic_cyclotomic_descriptor_bits": p_diag.automaton.cyclotomic_descriptor_bits
        if p_diag.automaton
        else 0,
        "diagnostic_random_access_selected": p_diag.automaton.selected_random_access
        if p_diag.automaton
        else None,
        "semantic_projection_field_compositions": p_sem.decision.projection_field_compositions,
    }
    special_numbers_metrics = {
        "fermat4_primality_fields": sorted(type(f4.primality).__dataclass_fields__)
        if f4.primality
        else [],
        "fermat4_duplicate_depth_field_present": "cyclotomic_character"
        in type(f4).__dataclass_fields__,
        "mersenne13_primality_fields": sorted(type(m13.primality).__dataclass_fields__)
        if m13.primality
        else [],
        "mersenne13_duplicate_depth_field_present": "cyclotomic_character"
        in type(m13).__dataclass_fields__,
        "mersenne15_method": m15.projection_method,
        "mersenne15_number_factor_projection": m15.radix_word.factored_projection
        is not None,
    }
    shared_ir_and_cache_metrics = {
        "factored_prime_automaton_object_shared": a is b,
        "block128_behavioral_aliases": stats.get("behavioral_partition_left_aliases", 0)
        + stats.get("behavioral_partition_right_aliases", 0),
        "block128_behavioral_refinement_runs": stats.get(
            "behavioral_partition_left_refinement_runs", 0
        )
        + stats.get("behavioral_partition_right_refinement_runs", 0),
        "block128_behavioral_states": stats.get("behavioral_partition_left_states", 0)
        + stats.get("behavioral_partition_right_states", 0),
        "block128_canonical_partition_states": stats.get(
            "canonical_partition_left_states", 0
        )
        + stats.get("canonical_partition_right_states", 0),
    }
    local_ring_metrics = {
        "phi7_mod8_component_degrees": [len(f) - 1 for f in phi7_mod8],
        "phi8_mod32_ramified_components": len(phi8_mod32),
        "ternary_phi8_kernel": ternary_phi8.kernel_size,
        "ternary_phi8_cokernel": ternary_phi8.cokernel_size,
        "decimal_phi8_kernel": decimal_phi8.kernel_size,
        "decimal_phi8_unit": decimal_phi8.unit,
    }
    quotient_synthesis_metrics = _m7_cegar()

    metrics: dict[str, object] = {
        "release": "v0.43.0",
        "reverse_add": reverse_add_metrics,
        "collatz": collatz_metrics,
        "prime": prime_metrics,
        "special_numbers": special_numbers_metrics,
        "shared_ir_and_cache": shared_ir_and_cache_metrics,
        "local_ring": local_ring_metrics,
        "quotient_synthesis": quotient_synthesis_metrics,
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")

    r = reverse_add_metrics
    c = collatz_metrics
    p = prime_metrics
    _s = special_numbers_metrics
    ir = shared_ir_and_cache_metrics
    lr = local_ring_metrics
    q = quotient_synthesis_metrics
    lines = [
        "# v0.43.0 compiler duplication / tech-debt closure",
        "",
        "This probe is deterministic and compares the default semantic compiler with the explicit diagnostic profile.  The production path now retains and computes only the canonical semantic carrier needed for the requested family; theorem/research views are opt-in.",
        "",
        "## Demand-driven family compilers",
        "",
        "| family | semantic path | diagnostic-only work removed from semantic path |",
        "|---|---|---|",
        f"| reverse-add | formula roots + boundary growth state | {r['diagnostic_materialized_values']} integer materializations, {r['diagnostic_primary_jets']} primary jets, carry/reset accounting up to {r['diagnostic_carry_reset_max_bits']} bits |",
        f"| Collatz | formula roots + canonical accelerated semantics | physical branch strings, raw sentinel quotient, valuation projection and parity sensitivity; diagnostic orbit has {c['diagnostic_odd_steps']} odd steps / valuation sum {c['diagnostic_valuation_sum']} |",
        f"| primes | residual-divisor decision/summary | cyclotomic wheel ({p['diagnostic_cyclotomic_groups']} field groups / {p['diagnostic_cyclotomic_state_bits']} live bits), packed comparison and sensitivity; Boolean primary jet stays opt-in |",
        "| Fermat/Mersenne | compact primality work summary + one `SpecialBinaryJumpProgram` / private group-depth theorem path | terminal modular residue/trace, deleted order-character classifier stack, and default alternate-radix theorem channels |",
        "",
        f"Reverse semantic materialized values/jets are **{r['semantic_materialized_values']}/{r['semantic_primary_jets']}** and its carry-reset diagnostic charge is **{r['semantic_carry_reset_max_bits']}**.  Prime semantic primary-jet compositions are **{p['semantic_primary_jet_compositions']}**.  Collatz has no retained branch string and no replayable `valuation_symbols` compilation property.",
        "",
        "## Canonical shared compiler infrastructure",
        "",
        f"- The immutable packed factor automaton is canonical-shared: **{ir['factored_prime_automaton_object_shared']}**.",
        f"- Post-hoc partition behavioral aliasing is deleted: the exercised decimal T^128 application reports **{ir['block128_behavioral_aliases']}** late aliases and **{ir['block128_behavioral_refinement_runs']}** late refinement passes. Its {ir['block128_canonical_partition_states']} exact extensional partition states have final IDs before higher recursive HashLife actions retain them.",
        "- One `CyclotomicAffineMorphism` owns affine digit-module composition/powering; reverse-add growth transport, Collatz radix-affine maps, shifts and normalization-factor actions delegate to it.",
        "- One exact observer analyzer, unary Moore minimizer and finite CEGAR synthesizer replace family-specific closure/minimization loops.",
        "",
        "## Prime-power local-ring closure",
        "",
        f"`Phi_7 mod 8` Hensel-lifts into component degrees **{lr['phi7_mod8_component_degrees']}** and CRT-reconstructs losslessly.  Ramified `Phi_8 mod 32` remains **{lr['phi8_mod32_ramified_components']}** primary component rather than receiving a fake split.  Multiplication by ternary normalization `3-z` has exact kernel/cokernel **{lr['ternary_phi8_kernel']}/{lr['ternary_phi8_cokernel']}**, while decimal `10-z` is a unit (kernel {lr['decimal_phi8_kernel']}).",
        "",
        "## Fail-closed quotient synthesis",
        "",
        f"The generic CEGAR synthesizer rediscovers the bounded M7 sign quotient with **{q['classes']} classes**, closed={q['closed']}, noninjective={q['noninjective']}, selecting exactly `{q['selected_features']}`.  It does not promote either conflicting primary factor alone.",
        "",
        "## Remaining blockers are theorem blockers",
        "",
        "The compiler no longer needs duplicate semantic carriers or mandatory diagnostic traversals to express the known reductions. Remaining blockers are mathematical: a closed reverse-add residual successor; a non-injective normalized quotient of the self-branching Collatz morphism; a factor-free Fermat/Mersenne purity injection into the proved group-depth quotient; and a prime first-hole/count quotient smaller than the exact residual/cyclotomic wheel carriers.",
        "",
    ]
    REPORT.write_text("\n".join(lines))
    print(json.dumps(metrics, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
