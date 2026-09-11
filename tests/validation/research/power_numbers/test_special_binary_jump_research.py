from devtools.experiments.power_numbers.bounded_jump_profile import (
    special_binary_jump_profiles,
)


def test_special_binary_jump_profiles_lock_real_temporal_jump_and_construction_blocker() -> (
    None
):
    rows = special_binary_jump_profiles()
    assert [
        (r.family, r.parameter, r.carrier_classes, r.quotient_classes) for r in rows
    ] == [
        ("fermat", 2, 3, 2),
        ("fermat", 3, 17, 5),
        ("fermat", 4, 2049, 12),
        ("mersenne", 5, 16, 5),
        ("mersenne", 7, 64, 7),
        ("mersenne", 11, 1024, 3),
        ("mersenne", 13, 4096, 13),
    ]
    assert all(r.specialization_raw_squarings == 0 for r in rows)
    assert all(
        r.binary_compositions <= 2 * max(1, r.quotient_steps.bit_length()) for r in rows
    )
    assert all(
        r.construction_is_exhaustive and not r.scalable_construction for r in rows
    )
    assert all(r.proof_states_examined > r.quotient_classes for r in rows)
