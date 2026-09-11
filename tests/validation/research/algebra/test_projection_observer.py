from devtools.experiments.algebra.projection_observer import (
    collatz_parity_observer_profile,
    fermat_squaring_observer_profile,
    mersenne_lucas_observer_profile,
    prime_lane_observer_profile,
    prime_wheel_observer_profile,
    reverse_add_admissible_growth_words,
    reverse_add_growth_observer_profile,
)


def test_reverse_add_growth_projection_is_three_element_block_monoid() -> None:
    p = reverse_add_growth_observer_profile()
    assert (p.scan_states, p.block_transformations, p.transformation_bits) == (2, 3, 2)
    assert reverse_add_admissible_growth_words(4).exact_projection_words == 15
    # Still exponential: the no-1111 theorem reduces the information rate but
    # does not produce a bounded future-growth observer.
    assert reverse_add_admissible_growth_words(20).required_bits >= 18


def test_collatz_future_parity_observer_has_no_nontrivial_universal_quotient() -> None:
    for width in range(1, 11):
        p = collatz_parity_observer_profile(width)
        assert p.exact_projection_words == 1 << width
        assert p.required_bits == width


def test_single_prime_lane_is_already_moore_minimal_in_its_residue_coordinate() -> None:
    for q in (3, 5, 7, 11, 31):
        p = prime_lane_observer_profile(q)
        assert p.source_states == p.observer_classes == q
        assert p.observer_bits == (q - 1).bit_length()


def test_raw_prime_wheel_needs_full_period_before_crt_factorization() -> None:
    for factors in ((3, 5), (3, 5, 7), (3, 5, 7, 11)):
        p = prime_wheel_observer_profile(factors)
        assert p.observer_classes == p.source_states


def test_fermat_prime_modulus_squaring_observer_collapses_to_logarithmic_class_bits() -> (
    None
):
    expected = {0: 2, 1: 3, 2: 5, 3: 9, 4: 17}
    for n, classes in expected.items():
        p = fermat_squaring_observer_profile(n)
        assert p.observer_classes == classes
        assert p.observer_bits <= n + 1


def test_lucas_lehmer_prime_modulus_observer_has_p_classes_but_composite_m11_collapses_to_sink() -> (
    None
):
    for exponent in (3, 5, 7, 13):
        p = mersenne_lucas_observer_profile(exponent)
        assert p.observer_classes == exponent
        assert p.initial_class is not None
    composite = mersenne_lucas_observer_profile(11)
    assert composite.observer_classes == 3
    # Initial LL state is in the never-zero sink class for M_11.
    assert composite.initial_class == 1
