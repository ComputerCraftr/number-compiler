from number_compiler.arithmetic.polynomials.primary_jet import primary_jet_from_digits
from number_compiler.sequences.prime.congruence import (
    compile_prime_block_factored_decision,
)
from number_compiler.sequences.prime.coordinates import (
    prime_block_summary_hyperbolic_packed,
)
from number_compiler.sequences.prime.lane_quotient import (
    compile_prime_block_lane_quotient,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


def test_residual_divisor_quotient_matches_two_independent_prime_projectors() -> None:
    start = 9_999_993
    for length in (64, 256, 1024, 4096):
        quotient = compile_prime_block_lane_quotient(start, length, base_period=(4,))
        bitmap = project_odd_prime_block(start, length)
        hyper = prime_block_summary_hyperbolic_packed(start, length)
        assert quotient.summary == bitmap.summary == hyper.summary
        assert quotient.domain_size == length
        assert quotient.canonical_lanes == len(bitmap.canonical_lanes)


def test_residual_divisor_quotient_moves_set_interfaces_before_candidate_leaves() -> (
    None
):
    start = 9_999_993
    quotient = compile_prime_block_lane_quotient(start, 4096, base_period=(4,))
    packed = compile_prime_block_factored_decision(start, 4096, base_period=(4,))
    assert quotient.summary_count == packed.summary_count == 503
    assert quotient.summary_first == packed.summary_first == 13
    # Same finite Boolean function, but the divisor-set morphism avoids one
    # packed-residue transition per group per candidate-tree edge.
    assert quotient.lane_transform_checks < packed.congruence_transitions // 8
    assert quotient.decision_nodes <= packed.decision_nodes
    assert quotient.projection_work < packed.congruence_transitions


def test_mixed_radix_exact_tail_removes_gratuitous_1024_padding() -> None:
    start = 9_999_993
    lane = compile_prime_block_lane_quotient(start, 1024, base_period=(4, 2, 8))
    packed = compile_prime_block_factored_decision(start, 1024, base_period=(4, 2, 8))
    assert lane.position_bases == packed.position_bases == (4, 2, 8, 4, 2, 2)
    assert lane.domain_size == packed.domain_size == 1024
    assert lane.summary_count == packed.summary_count == 125
    assert lane.summary_first == packed.summary_first == 13
    assert packed.congruence_transitions < 200_000


def test_prime_boolean_primary_jet_is_composed_from_quotient_not_bitmap() -> None:
    start = 9_999_993
    length = 256
    quotient = compile_prime_block_lane_quotient(start, length, base_period=(4,))
    # Independent test-only materialization of the finite truth vector.
    bitmap = project_odd_prime_block(start, length)
    digits = tuple((bitmap.prime_mask >> j) & 1 for j in range(length))
    explicit = primary_jet_from_digits(digits, degree=4, modulus=32)
    assert explicit is not None
    assert quotient.primary_jet is not None
    assert quotient.primary_jet.jet == explicit.jet
    assert quotient.primary_jet is not None
    assert quotient.primary_jet.length == length


def test_irreducible_factor_basis_prunes_even_divisors_before_packed_gcd_work() -> None:
    quotient = compile_prime_block_lane_quotient(9_999_993, 4096, base_period=(4,))
    assert quotient.canonical_lanes == 446
    assert quotient.factor_generator_groups == 78
    assert quotient.factor_candidates == 1_581
    assert quotient.factor_generator_gcd_calls == 17_054
    # Odd candidate blocks cannot have an even prime factor.  The generator
    # drops that impossible branch before packed gcd state is constructed,
    # then discovers the same 446 canonical lanes.
    assert quotient.factor_generator_gcd_calls < 18_000


def test_single_lane_radix_morphisms_are_reused_before_interface_construction() -> None:
    quotient = compile_prime_block_lane_quotient(9_999_993, 4096, base_period=(4,))
    # The exact decision object is unchanged, but repeated period/phase actions
    # are now hash-consed before child interfaces are built.  Cache-hit lookup
    # work remains charged in projection_work; arithmetic child checks are not
    # repeated on hits.
    assert quotient.summary_count == 503
    assert quotient.summary_first == 13
    assert quotient.lane_transform_cache_hits > 1_000
    assert quotient.point_transform_cache_hits > 5_000
    assert quotient.transform_cache_hits > 7_000
    assert quotient.lane_transform_checks < 10_000
    assert quotient.radix_projection_work < 18_000
    assert quotient.projection_work < 40_000
