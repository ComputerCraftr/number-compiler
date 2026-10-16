"""Independent literal words check cyclic counts and powered spatial joins."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.carry.signed_phase import (
    BinaryPhaseCarryAction,
    SymbolicPhaseInterval,
    phase_capacity,
    signed_phase_fold,
)


def test_phase_actions_match_literal_words_and_all_carry_seams() -> None:
    for width in range(7):
        for value in range(1 << width):
            full = BinaryPhaseCarryAction.from_word(value, width, 4)
            assert signed_phase_fold(full.source_counts, 4) == value % 17
            for incoming in range(3):
                quotient, remainder = divmod(3 * value + incoming, 1 << width)
                assert full.carry_out[incoming] == quotient
                assert (
                    signed_phase_fold(full.output_counts[incoming], 4) == remainder % 17
                )
            split = width // 2
            low = BinaryPhaseCarryAction.from_word(value % (1 << split), split, 4)
            high = BinaryPhaseCarryAction.from_word(value >> split, width - split, 4)
            assert low.then(high) == full


def test_spatial_power_and_identity_preserve_phase_and_boundary_carry() -> None:
    atom = BinaryPhaseCarryAction.from_word(5, 3, 4)
    for copies in range(12):
        source = sum(5 << (3 * i) for i in range(copies))
        assert atom.power(copies) == BinaryPhaseCarryAction.from_word(
            source, 3 * copies, 4
        )
    huge = atom.power(10**12)
    assert huge.width == 3 * 10**12
    huge.verify()
    assert atom.power(3).then(atom.power(5)) == atom.power(8)


def test_unknown_interval_is_a_capacity_not_a_filled_source() -> None:
    interval = SymbolicPhaseInterval.from_interval(13, 10**12, 16)
    assert sum(interval.source_capacity) == 10**12
    assert interval.possible_carry_capacity == tuple(
        2 * n for n in interval.source_capacity
    )
    for start in range(7):
        expected = [0] * 8
        for position in range(start, start + 23):
            expected[position % 8] += 1
        assert phase_capacity(start, 23, 4) == tuple(expected)


def test_phase_actions_reject_forged_identity_and_unbounded_work() -> None:
    identity = BinaryPhaseCarryAction.identity(4)
    with pytest.raises(ArithmeticError, match="identity"):
        replace(identity, carry_out=(1, 1, 2)).then(identity)
    with pytest.raises(ValueError):
        BinaryPhaseCarryAction.from_word(0, 10**12, 4)
    with pytest.raises(ValueError, match="budget"):
        identity.power(1 << 4096)
    with pytest.raises(ValueError):
        BinaryPhaseCarryAction.from_word(True, 1, 4)
    with pytest.raises(ValueError):
        identity.power(True)
