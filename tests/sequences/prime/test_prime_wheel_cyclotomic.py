from number_compiler.sequences.prime.set import (
    canonical_multiplicative_lane_basis,
    smallest_factor,
)
from number_compiler.sequences.prime.wheel_cyclotomic import (
    build_prime_wheel_cyclotomic_automaton,
)


def test_cyclotomic_wheel_field_groups_exactly_classify_finite_block() -> None:
    start, length = 9_999_993, 256
    basis = canonical_multiplicative_lane_basis(start, length)
    automaton = build_prime_wheel_cyclotomic_automaton(basis.lanes)
    assert automaton.lane_count == len(basis.lanes)
    assert len(automaton.groups) < len(basis.lanes)
    assert automaton.state_bits > 0
    for index in range(length):
        prime, _calls = automaton.classify_index(index)
        assert prime == (smallest_factor(start + 2 * index) is None)


def test_cyclotomic_wheel_advance_is_random_access_group_action() -> None:
    start, length = 999_993, 128
    basis = canonical_multiplicative_lane_basis(start, length)
    automaton = build_prime_wheel_cyclotomic_automaton(basis.lanes)
    zero = automaton.zero()
    a = automaton.advance(zero, 17)
    b = automaton.advance(automaton.advance(zero, 5), 12)
    assert a == b
    assert a.index == 17
    assert automaton.classify_state(a) == automaton.classify_index(17)
