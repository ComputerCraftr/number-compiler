"""Signed affine corrections preserve the common high-digit cut."""

from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from math import floor

import pytest

from number_compiler.arithmetic.fields.affine_high_digits import (
    affine_high_digit_transport,
)


@pytest.mark.parametrize("offset", (-11, -7, -3, 1, 5, 49))
def test_signed_offset_transports_the_source_product_at_one_cut(offset: int) -> None:
    source_product = 3 * 5
    endpoint = (source_product + offset) // 4
    packet = affine_high_digit_transport(endpoint, offset, 2, 2)
    homogeneous = floor(Fraction(source_product, 4))
    assert homogeneous == 3
    assert packet.offset_quotient == endpoint - homogeneous
    assert packet.endpoint_width == endpoint.bit_length()
    assert packet.homogeneous_floor_width == homogeneous.bit_length()
    assert packet.homogeneous_high_prefix == homogeneous >> packet.cut_bit
    assert packet.endpoint_high_prefix == endpoint >> packet.cut_bit
    assert packet.signed_carry_into_high == (
        (endpoint >> packet.cut_bit) - (homogeneous >> packet.cut_bit)
    )
    assert packet.xor_mask == (
        (endpoint >> packet.cut_bit) ^ (homogeneous >> packet.cut_bit)
    )


def test_high_carry_preserves_width_change_and_negative_borrow() -> None:
    growth = affine_high_digit_transport(4, 1, 2, 2)
    assert (growth.cut_bit, growth.homogeneous_high_binary) == (1, "01")
    assert (growth.endpoint_high_binary, growth.high_xor_binary) == ("10", "11")
    assert growth.signed_carry_into_high == 1
    borrow = affine_high_digit_transport(2, -7, 2, 2)
    assert borrow.signed_carry_into_high == -1
    assert borrow.homogeneous_high_binary == "11"
    assert borrow.endpoint_high_binary == "10"


def test_huge_division_count_uses_signed_shift_without_power_allocation() -> None:
    packet = affine_high_digit_transport(2, 1, 10**100, 3)
    assert packet.offset_quotient == 1
    assert packet.homogeneous_high_binary == "001"
    assert packet.endpoint_high_binary == "010"


def test_high_digit_boundary_rejects_coercion_and_unbounded_render_width() -> None:
    with pytest.raises(TypeError):
        affine_high_digit_transport(True, 0, 0)
    with pytest.raises(ValueError, match="negative homogeneous"):
        affine_high_digit_transport(1, 8, 1)
    packet = affine_high_digit_transport(1, 0, 0)
    with pytest.raises(ValueError):
        replace(packet, prefix_width=10**100)
    with pytest.raises(ValueError, match="inconsistent"):
        replace(packet, signed_carry_into_high=1)
