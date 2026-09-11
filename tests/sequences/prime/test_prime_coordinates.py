from math import gcd

import pytest

from number_compiler.projection.radix_decision import bitmap_radix_decision_metrics
from number_compiler.sequences.prime.coordinates import (
    prime_pair_field,
    project_least_factor_field,
)
from number_compiler.sequences.prime.encoding_analysis import (
    factor_coordinate_period_metrics,
    project_prime_power_radix_metrics,
    zeckendorf_bitmap_decision_metrics,
    zeckendorf_digits,
    zeckendorf_weights,
)
from number_compiler.sequences.prime.set import project_odd_prime_block
from number_compiler.sequences.prime.wheel import (
    build_lcm_wheel,
    first_prime_lcm_wheel,
    project_odd_prime_block_lcm_wheel,
)


def test_prime_pair_field_carry_normalization_and_residue_telescope() -> None:
    for base in (2, 3, 5, 10, 16, 64):
        for origin, offset in ((9_999_991, 28), (999, 37), (12345, 6789), (0, 0)):
            field = prime_pair_field(origin, offset, base=base)
            assert field.raw_value() == origin + offset
            assert field.normalized_value() == origin + offset
            assert all(c in (0, 1) for c in field.carries)
            for modulus in (3, 5, 7, 97, 1009):
                assert field.residue(modulus) == (origin + offset) % modulus


@pytest.mark.validation  # Exhaustive certified wheel domain through 10,200.
def test_lcm_wheel_is_exact_prime_classifier_on_its_certified_domain() -> None:
    wheel = build_lcm_wheel(100)
    assert wheel.modulus_bits == 136
    assert wheel.update_events == 35
    for n in range(101, 10_201):
        if n > wheel.exact_high:
            break
        direct_composite = any(n % d == 0 for d in range(2, int(n**0.5) + 1))
        assert wheel.is_prime(n) == (not direct_composite)


@pytest.mark.validation  # Full 4,096-cell wheel/block integration.
def test_lcm_wheel_reproduces_block_summary_and_first_hole() -> None:
    start = 9_999_993
    length = 4096
    wheel_projection = project_odd_prime_block_lcm_wheel(start, length)
    lane_projection = project_odd_prime_block(start, length)
    assert wheel_projection.summary == lane_projection.summary
    assert wheel_projection.wheel_bits == 4529
    assert wheel_projection.wheel_update_events == 484
    first = first_prime_lcm_wheel(start, length)
    assert first.first_index == 13
    assert first.first_value == 10_000_019
    assert first.gcd_calls == 14


@pytest.mark.validation  # Nested exact windows through 4,096 prime coordinates.
def test_least_factor_tropical_envelope_removes_finite_window_redundancy() -> None:
    start = 9_999_993
    expected = {
        16: (17, 9),
        64: (54, 25),
        256: (150, 54),
        1024: (317, 124),
        4096: (446, 271),
    }
    for length, (periodic, active) in expected.items():
        result = project_least_factor_field(start, length)
        assert result.periodic_lanes == periodic
        assert result.active_lane_count == active
        assert result.summary == project_odd_prime_block(start, length).summary
        for j, factor in enumerate(result.labels):
            n = start + 2 * j
            if factor:
                assert n % factor == 0
                assert all(n % d for d in range(2, factor))


@pytest.mark.validation  # Three complete 4,096-cell decision-DAG constructions.
def test_power_of_two_radices_charge_child_references_not_only_nodes() -> None:
    start = 9_999_993
    m2 = project_prime_power_radix_metrics(start, 4096, 2)
    m4 = project_prime_power_radix_metrics(start, 4096, 4)
    m8 = project_prime_power_radix_metrics(start, 4096, 8)
    assert (m2.finite_lanes, m2.reachable_nodes, m2.reachable_child_refs) == (
        271,
        456,
        912,
    )
    assert (m4.reachable_nodes, m4.reachable_child_refs) == (241, 964)
    assert (m8.reachable_nodes, m8.reachable_child_refs) == (127, 1016)
    # Higher radix shrinks node identities but does not shrink the actual child-reference payload.
    assert m2.reachable_child_refs < m4.reachable_child_refs < m8.reachable_child_refs
    assert m2.or_calls < m4.or_calls < m8.or_calls


@pytest.mark.validation  # Full 4,096-cell binary/Zeckendorf decision comparison.
def test_zeckendorf_encoding_is_exact_but_not_a_smaller_prime_decision_domain_here() -> (
    None
):
    start = 9_999_993
    length = 4096
    projection = project_odd_prime_block(start, length)
    weights = zeckendorf_weights(length - 1)
    for value in (0, 1, 2, 17, 255, 4095):
        digits = zeckendorf_digits(value, weights)
        assert sum(bit * weight for bit, weight in zip(digits, weights)) == value
        assert all(not (digits[i] and digits[i + 1]) for i in range(len(digits) - 1))
    fib = zeckendorf_bitmap_decision_metrics(
        projection.composite_mask, length, order="msb"
    )
    binary = bitmap_radix_decision_metrics(projection.composite_mask, 12, order="msb")
    assert fib.nonterminal_nodes == 788
    assert binary.nonterminal_nodes == 456
    assert fib.nonterminal_nodes > binary.nonterminal_nodes


def test_fibonacci_modular_periods_do_not_collapse_factor_coordinates() -> None:
    metrics = factor_coordinate_period_metrics(9_999_993, 64, base=2)
    assert metrics.lane_count == 54
    assert metrics.pisano_sum > metrics.signed_order_sum
    assert metrics.distinct_pisano_periods > 1


@pytest.mark.validation  # Complete squarefree wheel construction through 3,163.
def test_squarefree_wheel_removes_prime_power_duplicates_without_prime_input() -> None:
    from number_compiler.sequences.prime.wheel import build_squarefree_wheel

    wheel = build_squarefree_wheel(3163)
    assert wheel.lcm_update_events == 484
    assert wheel.generator_events == 447
    assert wheel.modulus_bits == 4428
    # Same certified primality predicate as the larger lcm modulus.
    for n in (9_999_993, 10_000_019, 10_000_021, 10_008_181):
        assert wheel.is_prime(n) == (gcd(n, build_lcm_wheel(3163).modulus) == 1)


@pytest.mark.validation  # Full packed-wheel differential over 4,096 coordinates.
def test_finite_packed_wheel_discards_lane_identity_after_projection() -> None:
    from number_compiler.sequences.prime.wheel import build_finite_packed_prime_wheel

    start, length = 9_999_993, 4096
    wheel = build_finite_packed_prime_wheel(start, length)
    assert wheel.source_periodic_lanes == 446
    assert wheel.source_active_lanes == 271
    assert wheel.modulus_bits == 2515
    first, calls = wheel.first_prime()
    assert first == 13 and calls == 14
    projection = project_odd_prime_block(start, length)
    for j in range(length):
        assert wheel.is_prime_index(j) == (((projection.prime_mask >> j) & 1) == 1)


@pytest.mark.validation  # Complete 3,163-generator and 4,096-cell word-wheel query.
def test_word_packed_wheel_is_exact_and_uses_zero_one_carry_lanes() -> None:
    from number_compiler.sequences.prime.wheel import build_packed_wheel_program

    program = build_packed_wheel_program(3163, 63)
    assert program.generator_events == 447
    assert program.group_count == 78
    assert program.total_group_bits == 4465
    result = program.first_prime(9_999_993, 4096)
    assert result.first_index == 13
    assert result.first_value == 10_000_019
    assert result.gcd_calls == 122
    state = program.state_for(9_999_993)
    step = program.step2(state)
    assert all(c in (0, 1) for c in step.carries)
    assert step.state == program.state_for(9_999_995)


@pytest.mark.validation  # Full scalar and broadword wheel construction through 3,163.
def test_broadword_packed_step_matches_all_independent_word_lanes() -> None:
    from number_compiler.sequences.prime.wheel import (
        BroadwordPackedWheelProgram,
        build_packed_wheel_program,
    )

    broad = BroadwordPackedWheelProgram.build(3163)
    scalar = build_packed_wheel_program(3163, 62)
    assert broad.group_count == scalar.group_count == 78
    assert broad.packed_width_bits == 4992
    for n in (9_999_993, 10_000_017, broad.exact_high - 2):
        packed = broad.pack_state(n)
        step = broad.step2(packed)
        scalar_state = scalar.state_for(n)
        scalar_step = scalar.step2(scalar_state)
        assert broad.unpack_state(step.packed_residues) == scalar_step.state.residues
        assert step.carry_ones == scalar_step.carry_ones
        assert broad.classify_packed(packed) == scalar.classify_state(scalar_state)


@pytest.mark.validation  # Full 4,096-cell hyperbolic packed summary.
def test_hyperbolic_packed_least_factor_summary_needs_no_candidate_bitmap() -> None:
    from number_compiler.sequences.prime.coordinates import (
        prime_block_summary_hyperbolic_packed,
    )

    result = prime_block_summary_hyperbolic_packed(9_999_993, 4096)
    assert result.summary == project_odd_prime_block(9_999_993, 4096).summary
    assert result.summary.count == 503 and result.summary.first == 13
    assert result.generator_events == 447
    assert result.active_factor_count == 271
    assert result.cofactor_points == 7562
    assert result.roughness_word_gcds == 16234
    assert result.first_hole_word_gcds == 122
    assert result.packed_groups == 78


@pytest.mark.validation  # Complete generator discovery and extension through 3,200.
def test_self_modifying_packed_wheel_discovers_same_generators_without_lcm_state() -> (
    None
):
    from number_compiler.sequences.prime.wheel import (
        build_packed_wheel_program,
        build_self_modifying_packed_wheel,
    )

    selfmod = build_self_modifying_packed_wheel(3163, 62)
    reference = build_packed_wheel_program(3163, 62)
    assert selfmod.generator_count == 447
    assert selfmod.group_count == 78
    assert selfmod.moduli == reference.moduli
    assert selfmod.build_gcd_calls == 18635
    # Extension consumes only the new natural generators and keeps the same state object family.
    extended = selfmod.extend_to(3200)
    rebuilt = build_self_modifying_packed_wheel(3200, 62)
    assert extended.moduli == rebuilt.moduli
    assert extended.generator_count == rebuilt.generator_count
