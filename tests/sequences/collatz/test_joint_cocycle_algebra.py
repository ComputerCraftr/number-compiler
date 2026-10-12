"""Joint endpoint/sum actions preserve independently evaluated source cylinders."""

import pytest

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)


@pytest.mark.parametrize("source", (1, 2, 7, 27, 41, 97, 255))
@pytest.mark.parametrize("steps", (0, 1, 2, 8, 16, 32))
def test_joint_fields_match_normalized_successors_and_high_fiber(
    source: int, steps: int
) -> None:
    action = DyadicTerminalFieldAction.identity()
    current = source
    for _ in range(steps):
        atom = (
            DyadicTerminalFieldAction.one_run(1)
            if current & 1
            else DyadicTerminalFieldAction.zero_run(1)
        )
        action = action.then(atom)
        current = (3 * current + 1) // 2 if current & 1 else current // 2
    for receiving_source in (source, source + 5 * (1 << steps)):
        value, total, previous = receiving_source, 0, receiving_source
        for _ in range(steps):
            previous = value
            value = (3 * value + 1) // 2 if value & 1 else value // 2
            total += value
        assert action.certifies(receiving_source)
        assert action.endpoint(receiving_source) == value
        if steps:
            assert divmod(
                action.previous_gain * receiving_source + action.previous_offset,
                1 << (steps - 1),
            ) == (previous, 0)
        for modulus in (2, 7, 49, 257):
            assert action.sum_mod(receiving_source, modulus) == total % modulus
        if steps:
            with pytest.raises(ValueError, match="outside"):
                action.endpoint(receiving_source + 1)


def test_joint_composition_parenthesization_and_repeated_cycle() -> None:
    odd = DyadicTerminalFieldAction.one_run(1)
    even = DyadicTerminalFieldAction.zero_run(1)
    third = DyadicTerminalFieldAction.one_run(3)
    assert odd.then(even).then(third) == odd.then(even.then(third))
    cycle = odd.then(even)
    repeated = cycle.power(37)
    assert repeated.endpoint(1) == 1
    assert repeated.sum_mod(1, 257) == 111
    assert cycle.power(0) == DyadicTerminalFieldAction.identity()


def test_joint_coefficients_cannot_be_directly_issued() -> None:
    with pytest.raises(TypeError, match="checked producer"):
        DyadicTerminalFieldAction(1, 3, 1, 999, 999, 1, 0)
    with pytest.raises(ValueError, match="violates"):
        DyadicTerminalFieldAction.from_prefixes(((1, 0), (3, 7)))
