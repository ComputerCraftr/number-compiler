"""Algebra and materialization boundaries for supplied binary blocks."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields import boolean_counter
from number_compiler.arithmetic.fields.boolean_counter import (
    MAX_BOOLEAN_BLOCK_BITS,
    BinaryBooleanCarryAction,
)
from number_compiler.arithmetic.fields.walsh import WalshH5, walsh_h5_at_offset


def test_direct_block_reports_both_exact_carry_contexts() -> None:
    source, addend, width, modulus = 0b10110, 0b01101, 5, 97
    action = BinaryBooleanCarryAction.from_words(source, addend, width, modulus)
    mask = (1 << width) - 1
    for incoming in (0, 1):
        total = source + addend + incoming
        carry, output, xor_mask = action.apply_words(incoming)
        assert (carry, output, xor_mask) == (
            total >> width,
            total & mask,
            source ^ (total & mask),
        )
        carry_summary, delta, h5 = action.apply(incoming)
        assert carry_summary == carry
        assert delta == (output - source) % modulus
        assert h5 == WalshH5.from_mask(xor_mask, width)


def test_offset_h5_matches_the_same_bits_in_absolute_coordinates() -> None:
    mask, width, offset = 0b101101, 6, 11
    absolute = WalshH5.from_mask(mask << offset, width + offset)
    assert walsh_h5_at_offset(mask, width, offset) == WalshH5(
        0, absolute.phi2, absolute.phi3_a, absolute.phi3_b
    )


def test_composition_matches_one_supplied_concatenated_block() -> None:
    modulus = 257
    low = BinaryBooleanCarryAction.from_words(0b101, 0b011, 3, modulus)
    high = BinaryBooleanCarryAction.from_words(0b1101, 0b0110, 4, modulus)
    joined = low.then(high)
    direct = BinaryBooleanCarryAction.from_words(0b1101_101, 0b0110_011, 7, modulus)
    assert joined == direct
    with pytest.raises(ValueError, match="not retained"):
        joined.apply_words(0)


def test_huge_repeat_stays_symbolic_and_keeps_exact_summary() -> None:
    copies = 10**18
    modulus = 17
    block = BinaryBooleanCarryAction.from_words(1, 1, 2, modulus)
    repeated = block.repeat(copies)

    geometric = (pow(4, copies, modulus) - 1) * pow(3, -1, modulus) % modulus
    assert repeated.length == 2 * copies
    assert repeated.length % 6 == (2 * copies) % 6
    assert repeated.next_carries == (0, 0)
    assert repeated.deltas == (geometric, (geometric + 1) % modulus)
    assert repeated.harmonics[0].length_mod6 == repeated.length % 6
    with pytest.raises(ValueError, match="not retained"):
        repeated.apply_words(0)


def test_repeat_preflights_symbolic_length_before_composition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    length = 1 << 4_095
    phase = length % 6
    harmonic = WalshH5(phase, 0, 0, 0)
    action = BinaryBooleanCarryAction(17, length, (0, 0), (0, 0), (harmonic, harmonic))

    def forbid_power(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("repeat entered binary power before preflight")

    monkeypatch.setattr(boolean_counter, "binary_power", forbid_power)
    with pytest.raises(ValueError, match="repeated Boolean length"):
        action.repeat(2)


def test_direct_materialization_budget_is_checked_before_operand_mask() -> None:
    with pytest.raises(ValueError, match="operand width"):
        BinaryBooleanCarryAction.from_words(0, 0, MAX_BOOLEAN_BLOCK_BITS + 1, 17)
