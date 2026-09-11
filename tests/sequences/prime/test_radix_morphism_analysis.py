from number_compiler.sequences.prime.radix_morphism_analysis import (
    binary_digit_cyclotomic_metrics,
    mixed_radix_prime_residual_metrics,
    reinterpreted_prime_cyclotomic_metrics,
)


def test_special_prime_bitstrings_are_pure_cyclotomic_words() -> None:
    assert 5 in binary_digit_cyclotomic_metrics(31, max_order=32).cyclotomic_orders
    assert 7 in binary_digit_cyclotomic_metrics(127, max_order=32).cyclotomic_orders
    assert 16 in binary_digit_cyclotomic_metrics(257, max_order=32).cyclotomic_orders
    assert 32 in binary_digit_cyclotomic_metrics(65537, max_order=32).cyclotomic_orders
    assert binary_digit_cyclotomic_metrics(19, max_order=32).cyclotomic_orders == ()


def test_reinterpreted_prime_bits_do_not_become_a_pure_cyclotomic_classifier() -> None:
    m = reinterpreted_prime_cyclotomic_metrics(9_999_993, 1024, 5)
    assert m.ambiguous_classes > 0
    assert m.ambiguous_candidates > 0


def test_mixed_radix_prime_residual_is_analysis_only_and_charges_projection_basis() -> (
    None
):
    b = mixed_radix_prime_residual_metrics(9_999_993, 256, (2,))
    m = mixed_radix_prime_residual_metrics(9_999_993, 256, (4, 2, 8))
    assert b.projection_canonical_lanes == m.projection_canonical_lanes
    assert m.charged_description_bits < b.charged_description_bits
