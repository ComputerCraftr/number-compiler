import pytest

from devtools.verification.oracles.bounded_filtration import (
    bounded_candidate_image_filtration,
)
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    HigherTwoPowerCharacterUnavailable,
    higher_two_power_character,
    outer_source_character,
    pure_two_primary_clock_shape,
    pure_two_primary_image_filtration,
)


def test_candidate_image_filtration_unifies_prime_and_composite_shapes() -> None:
    f4 = bounded_candidate_image_filtration("fermat", 4)
    assert f4.image_ranks == (
        2049,
        1025,
        513,
        257,
        129,
        65,
        33,
        17,
        9,
        5,
        3,
        2,
        2,
    )
    assert f4.pure_two_primary_shape
    assert f4.status == "prime"
    assert f4.source_target_hitting_time == 15
    assert f4.carrier_states_enumerated == 65537
    assert not f4.scalable_construction

    m11 = bounded_candidate_image_filtration("mersenne", 11)
    assert m11.image_ranks == (1024, 460, 282, 196, 196)
    assert m11.depth_strata == (564, 178, 86)
    assert m11.stable_image_states == 196
    assert m11.moore_classes == 3
    assert m11.image_depth_classes == 4
    assert not m11.moore_equals_image_depth
    assert not m11.pure_two_primary_shape
    assert m11.status == "composite"
    assert m11.source_target_hitting_time is None


def test_pure_theorem_is_the_zero_enumeration_specialization_of_same_object() -> None:
    for family, parameter in (("fermat", 4), ("mersenne", 13)):
        bounded = bounded_candidate_image_filtration(family, parameter)
        theorem = pure_two_primary_image_filtration(family, parameter)
        assert theorem.image_ranks == bounded.image_ranks
        assert theorem.depth_strata == bounded.depth_strata
        assert theorem.target_image_depths == bounded.target_image_depths
        assert theorem.moore_classes == bounded.moore_classes
        assert theorem.carrier_states_enumerated == 0
        assert theorem.scalable_construction
        assert theorem.target_distance_from_depth(0) == theorem.target_image_depth


def test_compact_clock_shape_matches_materialized_small_theorem() -> None:
    for family, parameter in (("fermat", 4), ("mersenne", 13)):
        shape = pure_two_primary_clock_shape(family, parameter)
        theorem = pure_two_primary_image_filtration(family, parameter)
        assert shape.modulus_bits == theorem.modulus_bits
        assert shape.observer_offset == theorem.observer_offset
        assert shape.target_depth == theorem.target_image_depth
        assert shape.quotient_classes == theorem.moore_classes
        assert shape.image_depth_classes == theorem.image_depth_classes
        assert shape.stable_image_states == theorem.stable_image_states
        clock_steps = shape.target_horizon - shape.observer_offset
        assert shape.target_after_clock_steps(clock_steps)
        assert not shape.target_after_clock_steps(clock_steps + 1)

    # This construction retains seven integers, not one row per depth.
    large = pure_two_primary_clock_shape("fermat", 20)
    assert large.quotient_classes == (1 << 20) - 20
    assert large.target_after_clock_steps(large.target_horizon - large.observer_offset)


def test_scalable_character_surface_is_fail_closed_beyond_proved_outer_layer() -> None:
    for family, parameter in (("fermat", 4), ("mersenne", 11), ("mersenne", 13)):
        outer = outer_source_character(family, parameter)
        assert outer.level == 1
        assert outer.membership is False
        assert outer.decided
    with pytest.raises(HigherTwoPowerCharacterUnavailable):
        higher_two_power_character("mersenne", 13, 2)
    with pytest.raises(HigherTwoPowerCharacterUnavailable):
        higher_two_power_character("fermat", 4, 2)


def test_outer_character_does_not_fake_classify_composite_m11_vs_prime_m13() -> None:
    m11 = outer_source_character("mersenne", 11)
    m13 = outer_source_character("mersenne", 13)
    assert m11.membership is False and m13.membership is False
    assert m11.method == m13.method == "jacobi-trace-preimage-boundary"
    assert bounded_candidate_image_filtration("mersenne", 11).status == "composite"
    assert bounded_candidate_image_filtration("mersenne", 13).status == "prime"
