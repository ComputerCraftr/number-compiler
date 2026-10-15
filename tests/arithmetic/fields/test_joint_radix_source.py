"""Independent finite-ring, source-sharing and nonunit guard regressions."""

from __future__ import annotations

from unittest.mock import patch

import pytest

from number_compiler.arithmetic.fields.integer_congruence import (
    affine_preimage,
    join_congruences,
)
from number_compiler.arithmetic.fields.three_power_radix import (
    RADICES,
    ThreePowerRadixOrbit,
    difference_power_block,
    triple_residue,
)
from number_compiler.arithmetic.fields.walsh import WalshH5, walsh64_mod5


@pytest.mark.parametrize("base", RADICES)
@pytest.mark.parametrize("clock", ("ordinary", "dyadic"))
def test_radix_tape_matches_independent_integer_sources(base: int, clock: str) -> None:
    for level in (1, 2, 5, 8):
        orbit = ThreePowerRadixOrbit(clock, level, base)
        exponent = level if clock == "ordinary" else 1 << level
        source = 3**exponent
        for row in orbit.tape(4):
            modulus = base**row.position
            residue = source % modulus
            assert row.source_remainder == residue
            assert row.tripling_carry == 3 * residue // modulus
            assert row.doubling_carry == 2 * residue // modulus
            assert row.tripling_sub_borrow == int((3 * residue) % modulus < residue)
            assert triple_residue(clock, level, base, row.position) == residue


def test_tape_recovers_only_one_widest_source() -> None:
    with patch(
        "number_compiler.arithmetic.fields.three_power_radix.triple_residue",
        wraps=triple_residue,
    ) as resolver:
        tape = ThreePowerRadixOrbit("dyadic", 1_000_000, 6).tape(64)
    assert len(tape) == 64
    resolver.assert_called_once_with("dyadic", 999_999, 6, 64)
    assert tape[-1].source_remainder % 3**64 == 0
    assert tape[-1].source_remainder % 2 == 1


@pytest.mark.parametrize("modulus", (5, 6, 10, 64, 1009))
def test_difference_cancellation_is_exact(modulus: int) -> None:
    for exponent in (0, 7, 40):
        for gap in (1, 2, 8):
            difference = 3 ** (exponent + gap) - 3**exponent
            value, valuation, normalized = difference_power_block(
                exponent, gap, modulus
            )
            assert value == difference % modulus
            assert valuation == (difference & -difference).bit_length() - 1
            assert normalized == (difference >> valuation) % modulus


def test_shared_walsh_transform_and_harmonic_composition() -> None:
    mask = 0x81F001239ABC4567
    transform = walsh64_mod5(mask)
    for column in range(64):
        inverse = (
            sum(
                (-1 if (row & column).bit_count() % 2 else 1) * transform[row]
                for row in range(64)
            )
            * 4
            % 5
        )
        assert inverse == (mask >> column) & 1
    left = WalshH5.from_mask(0b101, 3)
    right = WalshH5.from_mask(0b1101, 4)
    assert left.then(right) == WalshH5.from_mask(0b1101101, 7)
    assert left.repeat(7) == WalshH5.from_mask(
        sum(0b101 << (3 * i) for i in range(7)), 21
    )


def test_congruence_intersection_and_nonunit_affine_pullback() -> None:
    assert join_congruences((1, 6), (3, 10)) == (13, 30)
    assert join_congruences((0, 6), (1, 10)) is None
    for gain in (0, 3, 9, -3):
        for modulus in (3, 6, 10, 64):
            for residue in (0, 1):
                result = affine_preimage(
                    (residue, modulus), gain=gain, offset=5, denominator=4
                )
                for source in range(80):
                    numerator = gain * source + 5
                    expected = (
                        numerator % 4 == 0 and (numerator // 4) % modulus == residue
                    )
                    actual = result is not None and source % result[1] == result[0]
                    assert actual == expected


@pytest.mark.parametrize("bad", (True, -1, 1 << 64))
def test_walsh_rejects_non_bitmask_inputs(bad: int) -> None:
    with pytest.raises(ValueError):
        walsh64_mod5(bad)


def test_joint_ports_share_source_and_match_independent_masks() -> None:
    orbit = ThreePowerRadixOrbit("ordinary", 41, 10)
    with patch(
        "number_compiler.arithmetic.fields.three_power_radix.triple_residue",
        wraps=triple_residue,
    ) as resolver:
        ports = orbit.ordinary_ports(8)
    resolver.assert_called_once_with("ordinary", 40, 10, 8)
    assert ports.carry_word == orbit.carry_word(8)
    assert ports.add_borrow_mask == orbit.mask(8, "tripling_sub_borrow")
    assert ports.high_mask == orbit.mask(8, "tripling_high")
    assert ports.low_mask == orbit.mask(8, "tripling_low")
    assert ports.forward_borrow_mask == orbit.forward_mask(
        8, "forward_innovation_borrow"
    )
    assert ports.difference_xor_mask == orbit.forward_mask(8, "forward_difference_xor")
