from number_compiler.sequences.power_numbers.two_primary_clock import (
    DEAD_TWO_PRIMARY_SURVIVAL_DEPTH,
    PrimeTwoPrimaryPhaseOccurrence,
    bounded_prime_two_primary_depth_clock,
    mersenne_norm_one_multiply,
    mersenne_norm_one_trace,
    prime_two_primary_depth_clock_cache_info,
    two_primary_survival_depth_from_remaining,
    two_primary_survival_depth_view,
)


def test_phase_jump_rebases_depth_and_truncates_dead_odd_bits() -> None:
    source = PrimeTwoPrimaryPhaseOccurrence.from_phase("fermat", 4, 29)
    assert (source.depth, source.odd_phase, source.retained_phase_bits) == (0, 29, 16)
    jumped = source.jump(12)
    assert (jumped.depth, jumped.odd_phase, jumped.phase) == (12, 13, 13 << 12)
    assert jumped.retained_phase_bits == 4
    assert jumped.action_state == 4
    assert source.jump(10**12).phase == 0
    assert source.jump(10**12).action_state == 0

    huge = PrimeTwoPrimaryPhaseOccurrence.from_phase("fermat", 20, 1)
    assert huge.jump(10**12).odd_phase == 0
    try:
        _ = huge.phase
    except ValueError as error:
        assert error.args[0][0] == "two-primary-phase-materialization-budget"
    else:
        raise AssertionError("exact phase compatibility view must be physically gated")


def test_fermat_zero_remains_exact_occurrence_beside_shared_never_action() -> None:
    zero = PrimeTwoPrimaryPhaseOccurrence.from_phase(
        "fermat", 3, 0, exceptional_zero=True
    )
    one = PrimeTwoPrimaryPhaseOccurrence.from_phase("fermat", 3, 0)
    assert zero.action_state == one.action_state == 0
    assert zero.canonical_key != one.canonical_key
    assert zero.jump(10**12) == zero


def test_mersenne_trace_phase_canonicalizes_inversion_before_jump() -> None:
    left = PrimeTwoPrimaryPhaseOccurrence.from_phase("mersenne", 7, 3)
    right = PrimeTwoPrimaryPhaseOccurrence.from_phase("mersenne", 7, -3)
    assert left == right
    assert left.jump(5).phase == 1 << 5
    assert left.jump(5).terminal
    assert left.jump(10**12).phase == 0


def test_depth_machine_reuses_canonical_finite_unary_owner_and_cache() -> None:
    before = prime_two_primary_depth_clock_cache_info()
    first = bounded_prime_two_primary_depth_clock("fermat", 4)
    middle = prime_two_primary_depth_clock_cache_info()
    second = bounded_prime_two_primary_depth_clock("fermat", 4, max_classes=1_000)
    after = prime_two_primary_depth_clock_cache_info()
    assert first is second
    assert first.classes == 17
    assert after[0] == middle[0] + 1
    assert middle[0] + middle[1] >= before[0] + before[1]

    assert bounded_prime_two_primary_depth_clock("mersenne", 13).classes == 13
    try:
        bounded_prime_two_primary_depth_clock("fermat", 5, max_classes=16)
    except ValueError as error:
        assert error.args[0][0] == "two-primary-depth-clock-budget"
    else:
        raise AssertionError("bounded clock allocation must fail before construction")


def test_concrete_mersenne_circle_owner_has_norm_one_generator_and_trace_four() -> None:
    modulus = 31
    generator = (2, 1)
    squared = mersenne_norm_one_multiply(generator, generator, modulus)
    assert (
        generator[0] * generator[0] - 3 * generator[1] * generator[1]
    ) % modulus == 1
    assert mersenne_norm_one_trace(generator, modulus) == 4
    assert mersenne_norm_one_trace(squared, modulus) == (4 * 4 - 2) % modulus


def test_minimum_local_depth_owns_survival_tangent_and_curvature_views() -> None:
    first = two_primary_survival_depth_view((6, 1), 1)
    assert first.remaining == 1
    assert first.derived_views == (True, -1, 1)
    assert (first.remaining_delta, first.remaining_curvature) == (-1, 1)
    assert first.advance() is DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    assert DEAD_TWO_PRIMARY_SURVIVAL_DEPTH.derived_views == (False, 0, 0)

    # The deeper first component is irrelevant once minimum depth is known.
    assert first is two_primary_survival_depth_view((1, 1), 1)
    assert two_primary_survival_depth_view((6, 1), 2) is DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    assert (
        two_primary_survival_depth_view((0, 0, 1), 10**12)
        is DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    )


def test_survival_depth_jump_discards_dead_level_provenance() -> None:
    live = two_primary_survival_depth_view((11,), 1)
    assert live.remaining == 11
    assert live.advance(9).remaining == 2
    assert live.advance(10).curvature == 1
    assert live.advance(11) is DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    assert live.advance(10**12) is DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    assert (
        two_primary_survival_depth_from_remaining(0) is DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    )
    assert two_primary_survival_depth_from_remaining(11) is live


def test_survival_readout_differences_are_not_clipped_coordinate_differences() -> None:
    two = two_primary_survival_depth_from_remaining(2)
    one = two.advance()
    dead = one.advance()

    assert two.derived_views == (True, 0, -1)
    assert one.derived_views == (True, -1, 1)
    assert dead.derived_views == (False, 0, 0)
    assert two.remaining_delta == one.remaining_delta == -1
    assert dead.remaining_delta == 0
