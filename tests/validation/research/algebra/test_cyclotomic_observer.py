from devtools.experiments.algebra.cyclotomic_observer import (
    jet_unification_profile,
    mersenne_phi_sign_profile,
    normalization_defect_audit,
    reverse_cyclotomic_observer_profile,
    reverse_residual_successor_collisions,
    special_sign_quotient_work_profile,
)
from devtools.experiments.algebra.projection_observer import (
    special_square_sign_quotient_profile,
)
from number_compiler.arithmetic.carry.carry_normalization import (
    end_around_normalization_defect,
    linear_normalization_defect,
)
from number_compiler.arithmetic.fields.projection_field import (
    binomial_moments_from_values,
    cyclotomic_jet_from_values,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    binary_square_sign_representative,
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.arithmetic.polynomials.primary_jet import primary_jet_from_digits


def test_cyclotomic_jet_is_the_single_generalization_of_old_local_channels() -> None:
    values = (2, 15, 3, 2, 2, 3, 15, 2)
    for degree in range(1, 5):
        phi1 = cyclotomic_jet_from_values(values, order=1, power=degree, modulus=32)
        phi2 = cyclotomic_jet_from_values(values, order=2, power=degree, modulus=32)
        assert (
            phi1.local_linear_coefficients
            == binomial_moments_from_values(values, degree=degree, modulus=32).moments
        )
        assert (
            phi2.local_linear_coefficients
            == primary_jet_from_digits(values, degree=degree, modulus=32).jet
        )
    profile = jet_unification_profile(values)
    assert profile.phi1_equals_binomial and profile.phi2_equals_primary


def test_boundary_aware_normalization_defect_is_exact_in_linear_and_end_around_cases() -> (
    None
):
    raw = (2, 15, 3, 2, 2, 3, 15, 2)
    defect = linear_normalization_defect(raw, base=10)
    assert defect.identity_holds
    assert defect.boundary_in == defect.boundary_out == 0

    cyclic = cyclic_binary_square_add_projection(4, 5, -2)
    cdef = end_around_normalization_defect(cyclic.field, cyclic.normalization)
    assert cdef.identity_holds and cdef.boundary_vanishes_mod_end_around(1)

    exceptional = negacyclic_binary_square_projection(13, 4)
    ndef = end_around_normalization_defect(exceptional.field, exceptional.normalization)
    assert exceptional.normalization.exceptional_minus_one
    assert ndef.identity_holds and ndef.boundary_vanishes_mod_end_around(-1)

    audit = normalization_defect_audit()
    assert audit.exact
    assert audit.reverse_steps == audit.reverse_zero_boundary_padded_steps == 64
    assert audit.collatz_steps > 100


def test_reverse_196_collision_is_separated_by_existing_base_minus_residue_but_not_closed_by_one_small_jet() -> (
    None
):
    profile = reverse_cyclotomic_observer_profile()
    assert profile.collision_steps == (10, 11)
    assert profile.collision_action_equal and profile.collision_carry_equal
    assert profile.collision_base_minus_residues == (4, 8)
    assert profile.collision_pair_phi1_mod_base_minus == (8, 7)
    assert profile.existing_base_minus_separates
    assert profile.zero_conflict_candidates > 0
    assert profile.zero_conflict_noninjective_candidates == 0
    assert profile.minimum_zero_conflict_classes == 256
    # The same residue is not a universal hidden observer on nearby seeds.
    assert profile.neighboring_base_minus_conflicts > 0
    assert profile.neighboring_base_pm_conflicts > 0


def test_reverse_bounded_residual_candidates_are_not_successor_congruences() -> None:
    collisions = reverse_residual_successor_collisions()
    assert tuple(item.observer for item in collisions) == (
        "carry+base-minus",
        "carry+base-plus-minus",
        "carry+phi11-mod16",
    )
    assert all(item.is_successor_collision for item in collisions)
    assert (collisions[0].first_value, collisions[0].second_value) == (463, 382)
    assert (collisions[1].first_value, collisions[1].second_value) == (171017, 111221)
    assert (collisions[2].first_value, collisions[2].second_value) == (
        707471232064806,
        925271232062628,
    )


def test_mersenne_phi_p_mod2_is_exactly_the_sign_quotient_and_is_next_closed() -> None:
    for p, classes in ((5, 16), (7, 64), (11, 1024), (13, 4096)):
        profile = mersenne_phi_sign_profile(p)
        assert profile.phi_classes == profile.sign_classes == classes
        assert profile.same_partition
        assert profile.target_separating and profile.next_closed


def test_square_sign_canonicalization_is_exact_and_shared_tile_preserves_work_accounting() -> (
    None
):
    for width, sign, values in (
        (5, 1, range(31)),
        (4, -1, range(17)),
    ):
        modulus = (1 << width) - sign
        for value in values:
            representative = binary_square_sign_representative(value, width, sign)
            assert representative * representative % modulus == value * value % modulus

    m31 = special_sign_quotient_work_profile("mersenne", 31)
    assert m31.quotient_scalar_products < m31.baseline_scalar_products
    assert m31.quotient_coefficient_additions < m31.baseline_coefficient_additions
    assert m31.sign_quotient_steps > 0 and m31.nonzero_digits_saved > 0

    f5 = special_sign_quotient_work_profile("fermat", 5)
    assert f5.quotient_scalar_products < f5.baseline_scalar_products
    assert f5.quotient_coefficient_additions < f5.baseline_coefficient_additions
    assert f5.sign_quotient_steps > 0 and f5.nonzero_digits_saved > 0


def test_special_square_sign_observers_are_exact() -> None:
    for family, parameter in (
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 13),
        ("fermat", 2),
        ("fermat", 3),
    ):
        sign = special_square_sign_quotient_profile(family, parameter)
        assert sign.target_separating and sign.next_closed
