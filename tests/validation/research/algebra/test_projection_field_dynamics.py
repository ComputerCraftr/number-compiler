from devtools.experiments.algebra.projection_field_dynamics import (
    collatz_projection_field_profile,
    prime_projection_field_profile,
    reverse_add_projection_field_profile,
    special_digit_projection_feature_profile,
    special_projection_class_profile,
)


def test_reverse_add_current_projection_field_is_not_markov_for_decimal_196() -> None:
    p = reverse_add_projection_field_profile(196, steps=256)
    assert p.exact_actions == 255
    assert p.repeated_actions == 1
    assert p.conflicting_next_actions == 1
    assert p.transformed_feature_conflicts >= 1


def test_collatz_valuation_output_has_closed_exact_slab_but_linear_information() -> (
    None
):
    p = collatz_projection_field_profile(27)
    assert p.valuation_symbols == 41 and p.valuation_sum == 70
    assert p.exact_slab_bits < p.rle_description_bits
    assert p.raw_symbol_bits > 0
    assert len(p.odd_residue_maps) == 4


def test_prime_projection_output_channels_are_emitted_before_bitmap() -> None:
    p = prime_projection_field_profile(9_999_993, 64)
    assert (p.primes, p.first) == (3, 13)
    assert p.projection_field_compositions == 336
    assert p.boolean_theorem_bits < p.least_factor_rle_bits


def test_small_special_digit_channels_do_not_supply_exact_closed_target_observer() -> (
    None
):
    f = special_projection_class_profile("fermat", 4)
    m = special_projection_class_profile("mersenne", 13)
    assert f.observer_classes == 17 and m.observer_classes == 13
    for family, param in (("fermat", 3), ("mersenne", 7)):
        small = special_digit_projection_feature_profile(family, param, "phi2")
        assert not (small.target_separating and small.next_closed)
        exact = special_digit_projection_feature_profile(
            family, param, ("primary", "binomial", "phi2", "phi4", "phi8")
        )
        assert exact.target_separating and exact.next_closed
        assert exact.injective
