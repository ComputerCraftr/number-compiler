"""Behavioral compiler regressions, independent of source placement inventories."""

from __future__ import annotations

from typing import cast

from devtools.proofs import exact_oracle
from devtools.proofs.carry_action_quotient import (
    CarryThresholdSignature,
)
from devtools.proofs.oracles.special_binary_jump import (
    SpecialBinaryJumpProgram,
    build_fermat_binary_jump,
    build_mersenne_binary_jump,
)
from devtools.proofs.oracles.digit_power import (
    lucas_lehmer_digit_field,
    pepin_digit_field,
)
from devtools.proofs.quotient_synthesis import (
    ObserverFeature,
    synthesize_finite_quotient,
)
from devtools.proofs.sequence_diagnostics import with_carry_diagnostics
from devtools.proofs.special_power_monoid import (
    build_special_power_program,
)
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzCompilation,
    CollatzSequenceSpec,
    FermatSequenceSpec,
    MersenneSequenceSpec,
    PrimeBlockSequenceSpec,
    ReverseAddCompilation,
    ReverseAddSequenceSpec,
    SpecialDepthCertificateSummary,
)
from number_compiler.arithmetic.contracts.block_effect import _effect_key, _state_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.fields.congruence_automaton import (
    FactoredPrimeAutomaton,
)
from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
    cyclotomic_factors_mod_prime_power,
    cyclotomic_linear_factor_profile,
    cyclotomic_primary_components,
    polynomial_crt_mod_prime_power,
)
from number_compiler.arithmetic.polynomials.cyclotomic_family import (
    collatz_piecewise_cyclotomic_step,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.polynomial import (
    polynomial_multiply,
    polynomial_remainder_monic,
)
from number_compiler.sequences.collatz.orbit import COLLATZ_PIECEWISE_MORPHISM
from number_compiler.sequences.collatz.raw_field import (
    collatz_sentinel_orbit,
)
from number_compiler.sequences.prime.lane_quotient import (
    compile_prime_block_lane_quotient,
)


@exact_oracle()
def compiler_behavior_checks() -> dict[str, bool]:
    class Context:
        node_id = 1

    state_namespace_distinct = _state_key(1) != _state_key(Context())
    a = BaseBlockEffect(10)
    b = BaseBlockEffect(10)
    semantic_operator_key_equal = a.node_id != b.node_id and _effect_key(
        a
    ) == _effect_key(b)
    compiler = CanonicalSequenceCompiler()
    first = compiler.compile_diagnostic(ReverseAddSequenceSpec(196, 10, 2))
    second = compiler.compile_diagnostic(ReverseAddSequenceSpec(196, 10, 2))
    semantic_cache_reused = first is second and compiler.cache_size == 1
    lean = CanonicalSequenceCompiler()
    reverse_sem = lean.compile(ReverseAddSequenceSpec(196, 10, 8))
    reverse_diag = lean.compile_diagnostic(ReverseAddSequenceSpec(196, 10, 8))
    semantic_diagnostic_cache_separated = (
        reverse_sem is not reverse_diag
        and lean.cache_size == 2
        and all(
            term.value is None and term.primary_jet is None
            for term in reverse_sem.terms
        )
        and all(term.value is not None for term in reverse_diag.terms)
    )
    collatz_sem = lean.compile(CollatzSequenceSpec(27, 6, 128))
    prime_sem = lean.compile(PrimeBlockSequenceSpec(9_999_993, 64))
    fermat_sem = lean.compile(FermatSequenceSpec((4,), test_through=4))
    mersenne_sem = lean.compile(MersenneSequenceSpec((13, 15), test_through=15))
    semantic_views_are_lean = (
        reverse_sem.live_rows_average is None
        and reverse_sem.carry_reset_max_bits == 0
        and collatz_sem.branches == ()
        and collatz_sem.raw_field_quotient is None
        and collatz_sem.valuation_projection is None
        and collatz_sem.normalized_padic_radial is None
        and prime_sem.automaton is None
        and prime_sem.translation_sensitivity is None
        and prime_sem.decision.primary_jet is None
        and prime_sem.decision.primary_jet_compositions == 0
        and fermat_sem.terms[0].shifted_sensitivity is None
        and fermat_sem.terms[0].digit_projection is None
        and fermat_sem.terms[0].reinterpretations == ()
        and mersenne_sem.terms[0].successor_sensitivity is None
        and mersenne_sem.terms[0].digit_projection is None
        and mersenne_sem.terms[0].reinterpretations == ()
    )
    special_compact_results = (
        "status" in SpecialDepthCertificateSummary.__dataclass_fields__
        and "method" in SpecialDepthCertificateSummary.__dataclass_fields__
        and "residue" not in SpecialDepthCertificateSummary.__dataclass_fields__
        and "squarings" not in SpecialDepthCertificateSummary.__dataclass_fields__
        and not hasattr(fermat_sem.terms[0].primality, "residue")
        and not hasattr(mersenne_sem.terms[0].primality, "residue")
    )
    m15_sem = mersenne_sem.terms[1]
    mersenne_cheapest_proof_first = (
        m15_sem.projection_method == "deferred"
        and m15_sem.composite_exponent_factor is None
        and m15_sem.radix_word.factored_projection is None
        and m15_sem.source_guard is None
    )
    factored_automaton_is_canonical = FactoredPrimeAutomaton.build(
        1000
    ) is FactoredPrimeAutomaton.build(1000, word_bits=62)
    reverse_growth_itinerary_not_retained = (
        "growths" not in ReverseAddCompilation.__dataclass_fields__
    )
    proof_first = with_carry_diagnostics(first)
    reverse_growth_projection_reduced = (
        first.growth_state_max_bits < proof_first.carry_reset_max_bits
        and all(type(term.width) is int for term in first.terms)
        and tuple(first.growths)
        == tuple(
            cast(int, b.width) - cast(int, a.width)
            for a, b in zip(first.terms[:-1], first.terms[1:], strict=True)
        )
    )
    prime = compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, 64))
    prime_single_block_projection = (
        not hasattr(prime, "projection")
        and type(prime.decision).__name__ == "PrimeLaneQuotientCompilation"
    )
    prime_large = compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, 4096))
    prime_lane_action_reused = (
        prime_large.decision.transform_cache_hits > 5_000
        and prime_large.decision.lane_transform_checks < 10_000
        and prime_large.decision.radix_projection_work < 16_000
    )
    prime_radix_schedule_is_static = prime_large.decision.base_period == (4, 8)
    prime_odd_factor_branch_pruned_before_gcd = (
        prime_large.decision.factor_candidates == 1_581
        and prime_large.decision.factor_generator_gcd_calls == 17_054
        and prime_large.decision.canonical_lanes == 446
        and prime_large.decision.summary.count == 503
        and prime_large.decision.summary.first == 13
    )
    prime_ra = lean.compile(PrimeBlockSequenceSpec(9_999_993, 128, random_access=True))
    prime_cyclotomic_random_access_exact = (
        prime_ra.automaton is None
        and prime_ra.wheel_automaton is prime_ra.decision.wheel_cyclotomic
        and prime_ra.wheel_automaton is not None
        and prime_ra.decision.summary.first is not None
        and prime_ra.wheel_automaton.classify_index(prime_ra.decision.summary.first)[0]
    )
    prime_diag_uses_cyclotomic_not_boolean_jet = (
        prime.decision.primary_jet is None
        and prime.decision.primary_jet_compositions == 0
        and prime.automaton is not None
        and prime.automaton.start_primary_jet is None
        and prime.automaton.first_primary_jet is None
        and prime.automaton.cyclotomic_group_count > 0
    )
    prime_projection_algebra = compile_prime_block_lane_quotient(
        9_999_993, 64, base_period=(4,), projection_algebra=True
    )
    prime_projection_algebra_prebitmap = (
        prime_projection_algebra.binomial_moments is not None
        and len(prime_projection_algebra.cyclotomic_projection) == 3
        and prime_projection_algebra.projection_field_compositions > 0
    )
    prime_unused_output_algebra_not_retained = (
        prime.decision.binomial_moments is None
        and not prime.decision.cyclotomic_projection
        and prime.decision.projection_field_compositions == 0
    )
    carry_sig = CarryThresholdSignature.from_pair((2, 9, 14, 18, 14, 9, 2), base=10)
    carry_pair_symmetry_quotiented = (
        carry_sig.symmetric
        and carry_sig.description_bits < (10).bit_length() + 3 + 2 * 7
    )
    collatz = compiler.compile_diagnostic(CollatzSequenceSpec(27, 6, 200))
    fermat = compiler.compile_diagnostic(FermatSequenceSpec((4, 5), test_through=5))
    mersenne = compiler.compile_diagnostic(
        MersenneSequenceSpec((11, 31), test_through=31)
    )
    shared_sensitivity_attached = (
        collatz.normalized_padic_radial is not None
        and prime_large.translation_sensitivity is not None
        and fermat.terms[0].shifted_sensitivity is not None
        and mersenne.terms[1].successor_sensitivity is not None
    )
    special_digit_field_detached_from_compiler = all(
        term.digit_projection is None for term in fermat.terms
    ) and all(term.digit_projection is None for term in mersenne.terms)
    lazy_f5, lazy_m11 = (
        compiler.resolve_special_theorem("fermat", 5),
        compiler.resolve_special_theorem("mersenne", 11),
    )
    special_theorem_query_fails_closed = (
        fermat.terms[1].projection_method == "deferred"
        and fermat.terms[1].factor_witness is None
        and fermat.terms[1].radix_word.factored_projection is None
        and lazy_f5.projection_method.startswith("terminal-threshold:")
        and lazy_f5.factor_witness is None
        and lazy_f5.factored_projection is None
        and lazy_f5.primality is not None
        and lazy_f5.primality.status == "unknown"
        and not lazy_f5.primality.decided
        and lazy_f5.primality.target_depth is None
        and lazy_f5.primality.specialization_raw_squarings == 0
        and lazy_f5.source_guard.failure_bit is None
        and mersenne.terms[0].projection_method == "deferred"
        and lazy_m11.projection_method.startswith("terminal-threshold:")
        and lazy_m11.factor_witness is None
        and lazy_m11.factored_projection is None
        and lazy_m11.primality is not None
        and lazy_m11.primality.status == "unknown"
        and not lazy_m11.primality.decided
        and lazy_m11.primality.target_depth is None
        and lazy_m11.primality.specialization_raw_squarings == 0
        and lazy_m11.source_guard.failure_bit is None
    )
    sentinel27 = collatz_sentinel_orbit(27, base=4)
    collatz_sentinel_quotient_exact = (
        len(sentinel27) == 41
        and sum(step.valuation for step in sentinel27) == 70
        and max(step.scalar_carry_peak for step in sentinel27) <= 2
    )
    collatz_valuation_projection_attached = (
        collatz.valuation_projection is not None
        and collatz.raw_field_quotient is not None
        and collatz.valuation_projection.odd_steps
        == collatz.raw_field_quotient.odd_steps
        and collatz.valuation_projection.valuation_sum
        == collatz.raw_field_quotient.valuation_sum
    )
    collatz_linear_valuation_itinerary_not_retained = (
        "valuation_symbols" not in CollatzCompilation.__dataclass_fields__
        and not hasattr(CollatzCompilation, "valuation_symbols")
        and collatz.valuation_projection is not None
        and collatz.valuation_state_classes <= collatz.valuation_projection.odd_steps
        and collatz.valuation_state_max_bits > 0
    )
    special_power_f = build_special_power_program("fermat", 4, 15)
    special_power_m = build_special_power_program("mersenne", 31, 29)
    bounded_fermat_jump = build_fermat_binary_jump(4)
    bounded_mersenne_jump = build_mersenne_binary_jump(13)
    bounded_special_jump_is_real_but_non_scalable = (
        isinstance(bounded_fermat_jump, SpecialBinaryJumpProgram)
        and isinstance(bounded_mersenne_jump, SpecialBinaryJumpProgram)
        and bounded_fermat_jump.offset == 5
        and bounded_fermat_jump.carrier_classes == 2049
        and bounded_fermat_jump.quotient_classes == 12
        and bounded_fermat_jump.apply(15).quotient_steps == 10
        and bounded_fermat_jump.apply(15).specialization_raw_squarings == 0
        and bounded_mersenne_jump.carrier_classes == 4096
        and bounded_mersenne_jump.quotient_classes == 13
        and bounded_mersenne_jump.apply(11).specialization_raw_squarings == 0
        and bounded_fermat_jump.construction_is_exhaustive
        and bounded_mersenne_jump.construction_is_exhaustive
        and not bounded_fermat_jump.scalable_construction
        and not bounded_mersenne_jump.scalable_construction
        and bounded_fermat_jump.proof_states_examined
        >= bounded_fermat_jump.raw_source_states
        and bounded_mersenne_jump.proof_states_examined
        >= bounded_mersenne_jump.carrier_classes
    )
    special_power_monoid_fail_closed = (
        isinstance(special_power_f.operator, QuadraticPower)
        and isinstance(special_power_m.operator, QuadraticPower)
        and not hasattr(special_power_f, "node")
        and not hasattr(special_power_f, "arena_nodes")
        and special_power_f.steps == 15
        and special_power_f.construction_compositions < special_power_f.steps
        and special_power_f.raw_specialization_lower_bound == special_power_f.steps
        and not special_power_f.fast_raw_exact
        and special_power_f.prime_domain_image_classes() == 3
        and special_power_m.steps == 29
        and special_power_m.construction_compositions < special_power_m.steps
        and special_power_m.raw_specialization_lower_bound == special_power_m.steps
        and not special_power_m.fast_raw_exact
        and special_power_m.prime_domain_image_classes() == 3
    )
    m31_sign = lucas_lehmer_digit_field(31)
    f5_sign = pepin_digit_field(5)
    collatz_future_root_surface_exact = (
        tuple(root.local_shift for root in collatz.future_valuation_roots) == (0, 1)
        and tuple(root.radix4_period for root in collatz.future_valuation_roots)
        == ((0, 3, 1), (3, 0, 2))
        and collatz_sem.future_valuation_roots == ()
    )
    collatz_piecewise_successor_exact = (
        collatz.successor_morphism_key == COLLATZ_PIECEWISE_MORPHISM.canonical_key
        and all(
            collatz_piecewise_cyclotomic_step(value, order=8, modulus=32).exact
            for value in range(1, 65)
        )
    )
    lazy_f4, lazy_m31 = (
        compiler.resolve_special_theorem("fermat", 4),
        compiler.resolve_special_theorem("mersenne", 31),
    )
    special_certificate_unknown_without_recurrence = (
        fermat.terms[0].primality is None
        and mersenne.terms[1].primality is None
        and lazy_f4.primality is not None
        and lazy_f4.primality.status == "unknown"
        and not lazy_f4.primality.decided
        and lazy_f4.primality.target_depth is None
        and lazy_f4.primality.method.startswith("terminal-threshold:")
        and lazy_f4.primality.carrier_states_enumerated == 0
        and lazy_f4.primality.specialization_raw_squarings == 0
        and lazy_f4.source_guard.failure_bit is None
        and lazy_f4.factored_projection is None
        and lazy_m31.primality is not None
        and lazy_m31.primality.status == "unknown"
        and not lazy_m31.primality.decided
        and lazy_m31.primality.target_depth is None
        and lazy_m31.primality.method.startswith("terminal-threshold:")
        and lazy_m31.primality.carrier_states_enumerated == 0
        and lazy_m31.primality.specialization_raw_squarings == 0
        and lazy_m31.source_guard.failure_bit is None
        and lazy_m31.factored_projection is None
    )
    hensel7 = cyclotomic_factors_mod_prime_power(7, 2, 3)
    hensel_local_ring_exact = (
        len(hensel7) == 2 and len(cyclotomic_primary_components(8, 2, 5)) == 1
    )
    q8_source = (3, 5, 7, 1, 6, 2)
    q8_residues = tuple(
        polynomial_remainder_monic(q8_source, factor, modulus=8) for factor in hensel7
    )
    q8_rebuilt = polynomial_crt_mod_prime_power(q8_residues, hensel7, 2, 3)
    q8_whole: tuple[int, ...] = (1,)
    for factor in hensel7:
        q8_whole = polynomial_multiply(q8_whole, factor)
    hensel_local_ring_exact &= q8_rebuilt == polynomial_remainder_monic(
        q8_source, q8_whole, modulus=8
    )
    ternary_phi8 = cyclotomic_linear_factor_profile(8, 3, 32)
    normalization_singularity_profile_exact = (
        ternary_phi8.kernel_size == ternary_phi8.cokernel_size == 2
        and not ternary_phi8.unit
        and cyclotomic_linear_factor_profile(8, 10, 32).unit
    )
    factors7 = cyclotomic_factors_mod_prime(7, 2)
    cegar_features = tuple(
        ObserverFeature(
            f"phi7_factor_{i}",
            tuple(
                CyclotomicDigitBlock.from_coefficients(
                    digits_lsd(state, 2, 7),
                    order=7,
                    modulus=2,
                    factor=factor,
                    length=7,
                ).residue
                for state in range(127)
            ),
            cost=len(factor) - 1,
        )
        for i, factor in enumerate(factors7)
    )
    cegar_m7 = synthesize_finite_quotient(
        tuple((state * state - 2) % 127 for state in range(127)),
        tuple(state == 0 for state in range(127)),
        cegar_features,
    )
    finite_cegar_fail_closed_and_exact = (
        cegar_m7.closed
        and cegar_m7.noninjective
        and cegar_m7.classes == 64
        and len(cegar_m7.selected_features) == 2
    )
    special_square_sign_quotient_active = all(
        row.arithmetic_tile_steps == row.iterations
        and row.legacy_digit_convolution_calls == 0
        and row.scheduler_compositions == 0
        and row.sign_quotient_steps > 0
        for row in (m31_sign, f5_sign)
    )
    return {
        "prime_power_primary_roundtrip_and_ramification_guard_exact": hensel_local_ring_exact,
        "normalization_singular_kernel_cokernel_profile_exact": normalization_singularity_profile_exact,
        "bounded_special_binary_jump_real_but_non_scalable": bounded_special_jump_is_real_but_non_scalable,
        "special_power_monoid_compact_but_raw_specialization_fail_closed": special_power_monoid_fail_closed,
        "finite_cegar_rediscovers_m7_closed_sign_quotient": finite_cegar_fail_closed_and_exact,
        "typed_state_identifier_namespaces_distinct": state_namespace_distinct,
        "block_operator_cache_key_is_semantic": semantic_operator_key_equal,
        "sequence_cache_key_is_semantic": semantic_cache_reused,
        "semantic_and_diagnostic_cache_identities_separate": semantic_diagnostic_cache_separated,
        "semantic_compiler_views_are_demand_driven": semantic_views_are_lean,
        "special_compiler_drops_terminal_residue_and_trace": special_compact_results,
        "mersenne_raw_source_defers_even_cheap_theorem_rejection": mersenne_cheapest_proof_first,
        "factored_prime_automaton_is_canonical_shared_object": factored_automaton_is_canonical,
        "prime_compiler_retains_one_block_projection": prime_single_block_projection,
        "prime_lane_morphisms_quotient_before_interface_projection": prime_lane_action_reused,
        "prime_radix_schedule_is_static_semantic_policy": prime_radix_schedule_is_static,
        "prime_cyclotomic_random_access_reuses_decision_lane_scan": prime_cyclotomic_random_access_exact,
        "prime_default_diagnostic_uses_wheel_cyclotomics_not_boolean_jet": prime_diag_uses_cyclotomic_not_boolean_jet,
        "prime_projection_algebra_emitted_before_bitmap": prime_projection_algebra_prebitmap,
        "unused_prime_projection_algebra_not_retained": prime_unused_output_algebra_not_retained,
        "reverse_add_pair_symmetry_not_duplicated_in_carry_key": carry_pair_symmetry_quotiented,
        "shared_tropical_sensitivity_interface_attached": shared_sensitivity_attached,
        "special_number_raw_digit_projection_detached_from_compiler": special_digit_field_detached_from_compiler,
        "special_number_theorem_query_fails_closed_without_recurrence": special_theorem_query_fails_closed,
        "special_number_square_sign_quotient_reduces_digit_work": special_square_sign_quotient_active,
        "collatz_sentinel_quotient_avoids_carry_vector": collatz_sentinel_quotient_exact,
        "collatz_valuation_projection_monoid_attached": collatz_valuation_projection_attached,
        "collatz_future_root_surface_is_two_sector_and_diagnostic_only": collatz_future_root_surface_exact,
        "collatz_successor_is_self_branching_cyclotomic_operator": collatz_piecewise_successor_exact,
        "special_depth_certificate_unknown_without_classical_recurrence": special_certificate_unknown_without_recurrence,
        "reverse_growth_itinerary_not_retained": reverse_growth_itinerary_not_retained,
        "reverse_growth_projection_smaller_than_reset_signature": reverse_growth_projection_reduced,
        "collatz_linear_valuation_itinerary_not_retained": collatz_linear_valuation_itinerary_not_retained,
        "prime_odd_factor_branch_pruned_before_gcd": prime_odd_factor_branch_pruned_before_gcd,
    }
