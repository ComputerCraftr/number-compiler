"""Carry-first Euclidean reconstruction regressions, independent of admission."""

from __future__ import annotations

import ast
import builtins
import inspect
from math import gcd

import pytest

import tests.sequences.comma.c1_reconstruction_oracle as carry_oracle
from tests.sequences.comma.c1_reconstruction_oracle import (
    reconstruct_carry_first,
)

_SMOKE_WIDTHS = (5, 6, 7, 8, 9, 10, 11, 12, 13, 50, 100, 929, 100_000)


def _direct_small_reference(
    leading: int, suffix: int, width: int
) -> tuple[int, int, int, int, int, int]:
    """Literal small-width reference, allowed to form only q=5 or q=6 powers."""
    if width not in (5, 6):
        raise ValueError(
            "direct integer reference is restricted to widths five and six"
        )
    cycle_length = 10 // gcd(leading, 10)
    displacement = sum(
        10 * ((suffix % 10 + index * leading) % 10) + leading
        for index in range(cycle_length)
    )
    guard = 1 + int(leading < 9)
    scale = 10**width
    quotient, remainder = divmod(scale - suffix - guard, displacement)
    exponent = cycle_length * quotient
    current = suffix
    carry_count = 0
    for _ in range(exponent):
        raw = current + 10 * (current % 10) + leading
        carry_count += raw // 100
        current = raw % 100
    beta = (10 ** (width - 2) - carry_count) % 32
    headroom = 100 * beta - current
    return (
        quotient,
        remainder,
        exponent,
        current,
        carry_count,
        headroom,
    )


def test_q_five_and_q_929_share_packet_but_not_intermediate_carry_residue() -> None:
    short = reconstruct_carry_first(1, 0, 5)
    long = reconstruct_carry_first(1, 0, 929)

    assert 5 % 924 == 929 % 924
    assert (short.beta, short.target_suffix, short.reconstructed_headroom) == (
        2,
        20,
        180,
    )
    assert (long.beta, long.target_suffix, long.reconstructed_headroom) == (
        2,
        20,
        180,
    )
    assert short.exponent_mod_1600 == 570
    assert long.exponent_mod_1600 == 970
    assert short.carry_mod_32 == 6
    assert long.carry_mod_32 == 30


@pytest.mark.parametrize(
    ("leading", "suffix", "width"),
    [(1, 0, 5), (1, 83, 6), (4, 17, 5), (9, 3, 6)],
)
def test_small_width_packets_match_direct_integer_and_c1_reference(
    leading: int, suffix: int, width: int
) -> None:
    result = reconstruct_carry_first(leading, suffix, width)
    quotient, remainder, exponent, target, carries, headroom = _direct_small_reference(
        leading, suffix, width
    )
    modulus = 1600 * result.displacement

    assert result.quotient_mod_1600 == quotient % 1600
    assert result.remainder == remainder
    assert result.euclidean_residue_mod_1600p == (
        (10**width - suffix - result.guard) % modulus
    )
    assert result.exponent_mod_1600 == exponent % 1600
    assert result.target_suffix == target
    assert result.carry_mod_32 == carries % 32
    assert result.beta == (10 ** (width - 2) - carries) % 32
    assert result.reconstructed_headroom == headroom
    assert result.legacy_headroom == result.reconstructed_headroom


@pytest.mark.validation
def test_carry_first_euclidean_reconstruction_grid_without_decimal_powers() -> None:
    checked = 0
    for leading in range(1, 10):
        for suffix in range(99):
            for width in _SMOKE_WIDTHS:
                result = reconstruct_carry_first(leading, suffix, width)
                assert result.displacement > 0
                assert 0 <= result.quotient_mod_1600 < 1600
                assert 0 <= result.remainder < result.displacement
                assert (
                    result.quotient_mod_1600 * result.displacement + result.remainder
                    == result.euclidean_residue_mod_1600p
                )
                assert result.reconstructed_headroom == result.guard + result.remainder
                assert 1 <= result.beta <= 6
                checked += 1
    assert checked == 11_583


def test_huge_width_uses_modular_pow_calls_and_no_power_operator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_pow = builtins.pow

    def modular_only_for_huge_decimal_width(
        base: int, exponent: int, modulus: int | None = None
    ) -> int:
        if base == 10 and exponent > 1_000 and modulus is None:
            pytest.fail("carry-first reconstruction materialized a decimal power")
        if modulus is None:
            return int(original_pow(base, exponent))
        return int(original_pow(base, exponent, modulus))

    monkeypatch.setattr(builtins, "pow", modular_only_for_huge_decimal_width)
    result = reconstruct_carry_first(1, 0, 100_000)
    assert result.width == 100_000
    assert 0 <= result.exponent_mod_1600 < 1600
    module_tree = ast.parse(inspect.getsource(carry_oracle))
    assert not any(
        isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow)
        for node in ast.walk(module_tree)
    )


@pytest.mark.parametrize(
    ("leading", "suffix", "width"),
    [
        (True, 0, 5),
        (1, False, 5),
        (1, 0, True),
        (0, 0, 5),
        (1, 99, 5),
        (1, 0, 4),
    ],
)
def test_carry_first_reconstruction_rejects_invalid_exact_inputs(
    leading: int, suffix: int, width: int
) -> None:
    with pytest.raises((TypeError, ValueError)):
        reconstruct_carry_first(leading, suffix, width)
