"""Radial semantic identities describe multipliers, not event histories."""

from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.sequences.reverse_add.semantic_identity_cache import (
    build_radial_identity,
)


def test_equal_nonzero_multiplier_has_one_identity_across_exponent_histories() -> None:
    left = power_two_cyclotomic_radial_quotient(2, 2, 0, bits=3)
    right = power_two_cyclotomic_radial_quotient(2, 0, 4, bits=3)
    assert left.multiplier_residue() == right.multiplier_residue() == (4, 0)
    assert left.canonical_key == right.canonical_key
    assert build_radial_identity(left) == build_radial_identity(right)


def test_annihilated_multipliers_share_identity_without_losing_provenance() -> None:
    actions = (
        power_two_cyclotomic_radial_quotient(2, 3, 0, bits=3),
        power_two_cyclotomic_radial_quotient(2, 0, 6, bits=3),
        power_two_cyclotomic_radial_quotient(2, 0, 7, bits=3),
        power_two_cyclotomic_radial_quotient(2, 10**40, 0, bits=3),
    )
    assert len({action.canonical_key for action in actions}) == 1
    assert len({build_radial_identity(action) for action in actions}) == 1
    assert len({(action.no_growth, action.growth) for action in actions}) == len(
        actions
    )
