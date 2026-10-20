"""Adversarial checks for the bounded Mahler spatial carry quotient."""

import pytest

from devtools.experiments.antihydra.spatial_carry import (
    block_carry_action,
    compress_repeated_block,
)
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("multiplier", (3, 729))
def test_base64_block_actions_cover_every_port(multiplier: int) -> None:
    for value in range(64):
        action = block_carry_action(multiplier, 64, value)
        assert tuple(action.apply(c) for c in range(multiplier)) == tuple(
            (multiplier * value + c) // 64 for c in range(multiplier)
        )
        assert tuple(action.emit(c) for c in range(multiplier)) == tuple(
            (multiplier * value + c) % 64 for c in range(multiplier)
        )


@pytest.mark.parametrize("multiplier", (3, 729))
def test_adjacent_block_composition_matches_direct_integer_field(
    multiplier: int,
) -> None:
    samples = (0, 1, 7, 31, 63)
    ports = range(multiplier) if multiplier == 3 else (0, 1, 63, 64, 511, 728)
    for low in samples:
        low_action = block_carry_action(multiplier, 64, low)
        for high in samples:
            combined = low_action.then(block_carry_action(multiplier, 64, high))
            direct = block_carry_action(multiplier, 64**2, low + 64 * high)
            assert combined == direct
            assert tuple(combined.apply(c) for c in ports) == tuple(
                (multiplier * (low + 64 * high) + c) // 64**2 for c in ports
            )
            assert tuple(combined.emit(c) for c in ports) == tuple(
                low_action.emit(c)
                + 64
                * block_carry_action(multiplier, 64, high).emit(low_action.apply(c))
                for c in ports
            )


@pytest.mark.parametrize("multiplier,maximum_checked", ((3, 2), (729, 3)))
def test_checked_spatial_repetition_has_constant_work_after_fixed_carry(
    multiplier: int, maximum_checked: int
) -> None:
    ledger = ResourceLedger()
    for value in range(64):
        ports = range(multiplier) if multiplier == 3 else (0, 1, 63, 64, 511, 728)
        for incoming in ports:
            result = compress_repeated_block(
                multiplier, 64, value, incoming, 10**12, ledger
            )
            assert result.checked_steps <= maximum_checked
            assert result.repeated_count == 10**12 - len(result.transient)
            assert result.repeated_block is not None
            carry = incoming
            literal: list[int] = []
            for _ in range(result.checked_steps + 2):
                literal.append((multiplier * value + carry) % 64)
                carry = (multiplier * value + carry) // 64
            assert tuple(literal[: len(result.transient)]) == result.transient
            assert carry == result.outgoing_carry
            assert set(literal[len(result.transient) :]) == {result.repeated_block}
    assert ledger.counters["mahler_spatial_fixed_repetitions"] > 10**12


def test_zero_repetitions_validates_port_without_emitting() -> None:
    result = compress_repeated_block(729, 64, 63, 728, 0)
    assert result.transient == ()
    assert result.repeated_block is None
    assert result.repeated_count == 0
    assert result.outgoing_carry == 728
    with pytest.raises(ValueError, match="incoming carry"):
        compress_repeated_block(729, 64, 0, 729, 0)


def test_spatial_carry_equality_does_not_authorize_successor_merging() -> None:
    action = block_carry_action(729, 64, 5)
    assert action.apply(0) != action.apply(728)
    assert compress_repeated_block(729, 64, 5, 0, 20) != compress_repeated_block(
        729, 64, 5, 728, 20
    )
