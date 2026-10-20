from devtools.verification.oracles.special_classical_ceiling import (
    fermat_classical_ceiling,
    mersenne_classical_ceiling,
)
from devtools.verification.oracles.special_primality import (
    lucas_lehmer_test,
    pepin_test,
)


def test_fermat_classical_ceiling_matches_pepin_and_never_exceeds_bit_length_budget() -> (
    None
):
    for n in (1, 2, 3, 4, 5):
        got = fermat_classical_ceiling(n)
        ref = pepin_test(n)
        assert got.passes == ref.passes
        assert got.residue == ref.residue
        assert got.steps == ref.squarings == got.modulus_bits - 2
        assert got.factor_enumeration == 0
        assert got.carrier_states_enumerated == 0


def test_mersenne_classical_ceiling_matches_lucas_lehmer_and_never_exceeds_bit_length_budget() -> (
    None
):
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 31):
        got = mersenne_classical_ceiling(p)
        ref = lucas_lehmer_test(p)
        assert got.passes == ref.passes
        assert got.residue == ref.residue
        assert got.steps == ref.iterations == got.modulus_bits - 2
        assert got.factor_enumeration == 0
        assert got.carrier_states_enumerated == 0


def test_classical_ceiling_is_candidate_derived_target_defect_not_factor_slot_scan() -> (
    None
):
    f4 = fermat_classical_ceiling(4)
    f5 = fermat_classical_ceiling(5)
    m13 = mersenne_classical_ceiling(13)
    m11 = mersenne_classical_ceiling(11)
    assert f4.defect == 0 and f4.passes
    assert f5.defect != 0 and not f5.passes
    assert m13.defect == 0 and m13.passes
    assert m11.defect != 0 and not m11.passes
    assert all(row.gcd_packet is None for row in (f4, f5, m13, m11))
