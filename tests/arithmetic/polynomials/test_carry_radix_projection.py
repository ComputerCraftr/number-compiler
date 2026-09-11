from __future__ import annotations

from devtools.experiments.algebra.carry_radix_projection import (
    reverse_carry_radix_profile,
    special_carry_feature_closure_profile,
    special_combined_carry_digit_observer_profile,
)
from number_compiler.arithmetic.carry.carry_normalization import (
    end_around_carry_marker,
    normalization_carry_boundaries,
)
from number_compiler.arithmetic.fields.projection_field import (
    bounded_cyclotomic_factorization,
    offset_bit_planes,
    padded_radix_evaluation,
    reconstruct_offset_bit_planes,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)


def test_padded_alternate_radix_evaluation_recovers_leading_zeros_exactly() -> None:
    word = (0, 0, 1, 0, 0, 0, 0, 1, 0)
    for radix, expected in ((3, 732), (5, 15630), (7, 117656), (10, 1000010)):
        evaluated = padded_radix_evaluation(word, radix=radix)
        assert evaluated.value == expected
        assert evaluated.length == len(word)
        assert evaluated.leading_zero_padding == 2
        assert evaluated.recover_msf_values() == word


def test_lossless_bounded_cyclotomic_factorization_finds_196_step40_bridge() -> None:
    # Exact decimal-196 forward carry row at step 40, in boundary/string order.
    word = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0)
    factor = bounded_cyclotomic_factorization(word, order_limit=64)
    assert factor.leading_zero_padding == 3
    assert factor.trailing_zero_shift == 2
    assert factor.factors == ((2, 1), (6, 1), (10, 1), (30, 1))
    assert factor.residual_lsf == (1,)
    assert factor.fully_cyclotomic
    assert factor.recover_msf_values() == word
    for radix in (3, 5, 7, 10):
        evaluated = padded_radix_evaluation(word, radix=radix)
        divisor = (
            radix** factor.trailing_zero_shift
            * factor.evaluated_cyclotomic_factor(radix)
        )
        assert evaluated.value % divisor == 0


def test_offset_bit_planes_are_reversible_for_ternary_and_signed_carries() -> None:
    for field in ((0, 2, 1, 2, 0), (-4, -1, 3, 2, -4, 0)):
        offset, planes = offset_bit_planes(field)
        assert reconstruct_offset_bit_planes(offset, len(field), planes) == field


def test_end_around_internal_carries_are_derived_even_for_exceptional_minus_one() -> (
    None
):
    cyclic = cyclic_binary_square_add_projection(4, 5, -2)
    c = normalization_carry_boundaries(cyclic.field, cyclic.normalization)
    assert len(c) == 6
    assert c[0] == c[-1] == cyclic.normalization.boundary_in

    exceptional = negacyclic_binary_square_projection(13, 4)
    assert exceptional.normalization.exceptional_minus_one
    c = normalization_carry_boundaries(exceptional.field, exceptional.normalization)
    assert len(c) == 5
    assert c[0] == -1 and c[-1] == 1
    assert c[-1] == -c[0]


def test_reverse_carry_cyclotomic_coordinate_preserves_known_nonclosure() -> None:
    profile = reverse_carry_radix_profile(196, steps=64)
    assert profile.exact_current_rows == 63
    assert profile.repeated_current_rows == 1
    assert profile.different_next_conflicts == 1
    # A lossless factorization of the same current carry row cannot repair it.
    assert profile.factor_feature_conflicts >= 1
    samples = {step: factors for step, _word, factors, _evals in profile.sample_bridges}
    assert samples[40] == ((2, 1), (6, 1), (10, 1), (30, 1))
    assert samples[55] == ((5, 1), (25, 1))


def test_special_normalization_carry_is_not_the_missing_observer() -> None:
    fermat = special_carry_feature_closure_profile("fermat", 3)
    assert not fermat.exact_target_separating
    assert not fermat.exact_next_closed
    assert not fermat.cyclotomic_target_separating
    assert not fermat.cyclotomic_next_closed

    mersenne = special_carry_feature_closure_profile("mersenne", 5)
    assert mersenne.exact_target_separating
    assert not mersenne.exact_next_closed
    assert mersenne.cyclotomic_target_separating
    assert not mersenne.cyclotomic_next_closed


def test_carry_factors_can_help_one_small_mersenne_digit_observer_without_generalizing() -> (
    None
):
    # M5 is a real positive bridge: lossy Phi_2(state) + lossy carry factors is
    # a 29-class target-separating, next-closed refinement whose exact unary
    # Moore minimization recovers the known 5 target-observer classes.
    m5 = special_combined_carry_digit_observer_profile("mersenne", 5)
    assert m5.combined_classes == 29 < m5.source_states
    assert m5.target_separating and m5.next_closed and not m5.injective
    assert m5.minimized_observer_classes == 5

    # The same construction does not scale even one prime exponent further.
    m7 = special_combined_carry_digit_observer_profile("mersenne", 7)
    assert m7.combined_classes == 103 < m7.source_states
    assert m7.target_separating and not m7.next_closed
    assert m7.minimized_observer_classes is None

    f3 = special_combined_carry_digit_observer_profile("fermat", 3)
    assert not f3.target_separating and not f3.next_closed


def _marker_from_full_carries(carries: tuple[int, ...]) -> dict[str, int]:
    cs = tuple(map(int, carries))
    length = len(cs) - 1
    changes = [i for i in range(length) if cs[i + 1] != cs[i]]
    outgoing = cs[1:]
    nonzero = [i for i, c in enumerate(outgoing) if c]
    max_abs = max((abs(c) for c in outgoing), default=0)
    first_max = (
        next((i for i, c in enumerate(outgoing) if abs(c) == max_abs), length)
        if max_abs
        else length
    )
    return {
        "change_count": len(changes),
        "first_change": changes[0] if changes else length,
        "last_change": changes[-1] if changes else length,
        "nonzero_count": len(nonzero),
        "first_nonzero": nonzero[0] if nonzero else length,
        "max_abs_carry": max_abs,
        "first_max_abs": first_max,
        "carry_sum": sum(outgoing),
        "carry_moment": sum((i + 1) * c for i, c in enumerate(outgoing)),
    }


def test_end_around_marker_matches_full_carry_history_without_retaining_it() -> None:
    from number_compiler.arithmetic.polynomials.digit_convolution import (
        cyclic_binary_square_add_projection,
        negacyclic_binary_square_projection,
    )

    cases = []
    for value in range(31):
        cases.append(cyclic_binary_square_add_projection(value, 5, -2))
    for value in range(17):
        cases.append(negacyclic_binary_square_projection(value, 4))
    for projection in cases:
        carries = normalization_carry_boundaries(
            projection.field, projection.normalization
        )
        marker = end_around_carry_marker(projection.field, projection.normalization)
        expected = _marker_from_full_carries(carries)
        for key, value in expected.items():
            assert getattr(marker, key) == value
        assert marker.boundary_in == carries[0]
        assert marker.sign == projection.normalization.sign
        assert marker.length == len(projection.field)
        assert marker.phase(3) == (
            None if marker.first_change == marker.length else marker.first_change % 3
        )


def test_end_around_marker_is_logarithmic_scalar_summary_not_carry_payload() -> None:
    from number_compiler.arithmetic.polynomials.digit_convolution import (
        cyclic_binary_square_add_projection,
    )

    projection = cyclic_binary_square_add_projection(12345, 17, -2)
    marker = end_around_carry_marker(projection.field, projection.normalization)
    carries = normalization_carry_boundaries(projection.field, projection.normalization)
    assert not hasattr(marker, "carries")
    assert marker.description_bits < 20 * len(carries)
