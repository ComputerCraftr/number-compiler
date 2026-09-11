from tests.api.test_sequence_compiler import (
    test_block_cache_state_and_operator_keys_do_not_alias_numeric_namespaces,
    test_fermat_and_mersenne_are_actual_symbolic_radix_compilations_not_materialized_bitmaps,
    test_prime_and_collatz_use_same_compiler_without_cross_family_state_aliasing,
    test_sequence_compiler_uses_semantic_spec_keys_and_reuses_exact_result,
)
from tests.arithmetic.carry.test_carry_itinerary import (
    test_live_carry_itinerary_self_prunes_and_advances_without_discarded_rows,
    test_zplus1_primary_jet_is_exact_and_growth_is_literal_shift,
)
from tests.arithmetic.formula.test_core import (
    test_canonical_state_has_no_duplicate_state,
    test_deep_lazy_growth_has_no_recursion_failure,
    test_random_bases,
    test_synthesized_growth_and_successor_real_orbit,
)
from tests.arithmetic.polynomials.test_cyclotomic_special import (
    test_lucas_lehmer_quadratic_unit_conjugacy_and_known_cases,
    test_power_two_cyclotomic_closed_valuation_matches_expanded_negacyclic_kernel,
)
from tests.hashlife.actions.test_jump_contract import (
    test_binary_driver_has_no_scale_backend,
)
from tests.hashlife.actions.test_native_power import (
    test_native_four_step_matches_four_successors_random_bases,
    test_native_two_step_matches_two_successors_random_bases,
)
from tests.projection.test_radix_decision import (
    test_collatz_inverse_symbolic_dag_matches_truth_table_and_extends_without_enumeration,
)
from tests.sequences.collatz.test_collatz_pair import (
    test_accelerated_collatz_retains_only_the_latent_valuation_not_nested_lanes,
    test_decimal_mul3_digit_carries_form_exact_five_element_monoid,
)
from tests.sequences.collatz.test_collatz_parity import (
    test_native_parity_slab_composition_is_associative_and_concat_exact,
    test_physical_time_operator_composes_by_addition_in_parity_coordinate,
)
from tests.sequences.collatz.test_collatz_power import (
    test_collatz_powered_branch_dag_matches_reference_orbits,
)
from tests.sequences.prime.test_prime_automaton import (
    test_binary_cyclotomic_order_grouping_barely_compresses_prime_wheel,
    test_prime_boolean_block_has_no_constant_affine_coordinate_derivative,
)
from tests.sequences.prime.test_prime_binomial import (
    test_pascal_translation_mod_pow2_matches_exact_translation,
)
from tests.sequences.prime.test_prime_coordinates import (
    test_hyperbolic_packed_least_factor_summary_needs_no_candidate_bitmap,
    test_prime_pair_field_carry_normalization_and_residue_telescope,
    test_word_packed_wheel_is_exact_and_uses_zero_one_carry_lanes,
)
from tests.sequences.prime.test_prime_set import (
    test_prime_projection_reproduces_first_hole_and_canonical_lane_counts,
)

if __name__ == "__main__":
    test_canonical_state_has_no_duplicate_state()
    test_synthesized_growth_and_successor_real_orbit()
    test_random_bases()
    test_deep_lazy_growth_has_no_recursion_failure()
    test_binary_driver_has_no_scale_backend()
    test_native_two_step_matches_two_successors_random_bases()
    test_native_four_step_matches_four_successors_random_bases()
    test_collatz_powered_branch_dag_matches_reference_orbits()
    test_prime_projection_reproduces_first_hole_and_canonical_lane_counts()
    test_native_parity_slab_composition_is_associative_and_concat_exact()
    test_physical_time_operator_composes_by_addition_in_parity_coordinate()
    test_pascal_translation_mod_pow2_matches_exact_translation()
    test_prime_pair_field_carry_normalization_and_residue_telescope()
    test_word_packed_wheel_is_exact_and_uses_zero_one_carry_lanes()
    test_hyperbolic_packed_least_factor_summary_needs_no_candidate_bitmap()
    test_live_carry_itinerary_self_prunes_and_advances_without_discarded_rows()
    test_zplus1_primary_jet_is_exact_and_growth_is_literal_shift()
    test_decimal_mul3_digit_carries_form_exact_five_element_monoid()
    test_accelerated_collatz_retains_only_the_latent_valuation_not_nested_lanes()
    test_power_two_cyclotomic_closed_valuation_matches_expanded_negacyclic_kernel()
    test_lucas_lehmer_quadratic_unit_conjugacy_and_known_cases()
    test_binary_cyclotomic_order_grouping_barely_compresses_prime_wheel()
    test_prime_boolean_block_has_no_constant_affine_coordinate_derivative()
    test_collatz_inverse_symbolic_dag_matches_truth_table_and_extends_without_enumeration()
    test_sequence_compiler_uses_semantic_spec_keys_and_reuses_exact_result()
    test_block_cache_state_and_operator_keys_do_not_alias_numeric_namespaces()
    test_fermat_and_mersenne_are_actual_symbolic_radix_compilations_not_materialized_bitmaps()
    test_prime_and_collatz_use_same_compiler_without_cross_family_state_aliasing()
    print("canonical cross-family radix/cyclotomic sequence compiler selftest: ok")
