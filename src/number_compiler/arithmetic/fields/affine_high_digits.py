"""Exact aligned high-bit transport for an admitted affine integer action.

For ``y=(a*x+b)/2**d`` with an integral endpoint, the homogeneous quotient is
``floor(a*x/2**d) = y-ceil(b/2**d)``. This module observes the signed high-bit
carry across that common cut; it does not admit the source or action.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer

MAX_HIGH_DIGIT_WIDTH = 4096


@dataclass(frozen=True, slots=True)
class AffineHighDigitTransport:
    """Aligned high prefixes and the signed correction between them."""

    prefix_width: int
    cut_bit: int
    homogeneous_floor_width: int
    endpoint_width: int
    homogeneous_high_prefix: int
    endpoint_high_prefix: int
    offset_quotient: int
    signed_carry_into_high: int
    xor_mask: int

    def __post_init__(self) -> None:
        require_integer(
            self.prefix_width, "high-digit prefix width", 1, MAX_HIGH_DIGIT_WIDTH
        )
        require_integer(self.cut_bit, "high-digit cut", 0)
        require_integer(self.homogeneous_floor_width, "homogeneous width", 0)
        require_integer(self.endpoint_width, "endpoint width", 1)
        require_integer(self.homogeneous_high_prefix, "homogeneous prefix", 0)
        require_integer(self.endpoint_high_prefix, "endpoint prefix", 0)
        require_integer(self.offset_quotient, "offset quotient")
        require_integer(self.signed_carry_into_high, "signed high carry")
        require_integer(self.xor_mask, "high XOR mask", 0)
        if (
            self.homogeneous_high_prefix.bit_length() > self.prefix_width
            or self.endpoint_high_prefix.bit_length() > self.prefix_width
            or self.xor_mask.bit_length() > self.prefix_width
            or self.signed_carry_into_high
            != self.endpoint_high_prefix - self.homogeneous_high_prefix
            or self.xor_mask != self.homogeneous_high_prefix ^ self.endpoint_high_prefix
        ):
            raise ValueError("affine high-digit transport is internally inconsistent")

    @property
    def homogeneous_high_binary(self) -> str:
        return format(self.homogeneous_high_prefix, f"0{self.prefix_width}b")

    @property
    def endpoint_high_binary(self) -> str:
        return format(self.endpoint_high_prefix, f"0{self.prefix_width}b")

    @property
    def high_xor_binary(self) -> str:
        return format(self.xor_mask, f"0{self.prefix_width}b")


def affine_high_digit_transport(
    endpoint: int,
    offset: int,
    halvings: int,
    width: int = 8,
) -> AffineHighDigitTransport:
    """Observe a caller-authenticated ``(a*x+offset)/2**halvings`` endpoint.

    The caller must establish source admission and endpoint integrality first.
    The cut is shared by the homogeneous floor and endpoint, which preserves
    the signed carry even when the affine offset changes the bit width.
    """
    require_integer(endpoint, "affine endpoint", 1)
    require_integer(offset, "affine offset")
    require_integer(halvings, "affine dyadic divisions", 0)
    require_integer(width, "high-digit prefix width", 1, MAX_HIGH_DIGIT_WIDTH)
    # ceil(offset / 2**d), including negative offsets, without allocating 2**d.
    correction = -((-offset) >> halvings)
    homogeneous = endpoint - correction
    if homogeneous < 0:
        raise ValueError(
            "authenticated positive endpoint has negative homogeneous part"
        )
    cut = max(0, max(homogeneous.bit_length(), endpoint.bit_length()) - width)
    before = homogeneous >> cut
    after = endpoint >> cut
    return AffineHighDigitTransport(
        width,
        cut,
        homogeneous.bit_length(),
        endpoint.bit_length(),
        before,
        after,
        correction,
        after - before,
        before ^ after,
    )


__all__ = ["AffineHighDigitTransport", "affine_high_digit_transport"]
