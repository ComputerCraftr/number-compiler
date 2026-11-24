"""Ordered affine value responses. Source guard authority belongs to callers."""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Self


@dataclass(frozen=True, slots=True)
class AffinePortAction:
    modulus: int | None
    gain: int
    carry: int

    def __post_init__(self) -> None:
        if type(self.gain) is not int or type(self.carry) is not int:
            raise TypeError("affine port coefficients must be exact integers")
        modulus = self.modulus
        if modulus is not None and (
            type(modulus) is not int
            or modulus < 1
            or not 0 <= self.gain < modulus
            or not 0 <= self.carry < modulus
        ):
            raise ValueError("affine port coefficients must be reduced in their ring")

    @classmethod
    def reduced(cls, modulus: int, gain: int, carry: int) -> Self:
        if type(modulus) is not int or modulus < 1:
            raise ValueError("affine port modulus must be a positive integer")
        if type(gain) is not int or type(carry) is not int:
            raise TypeError("affine port coefficients must be exact integers")
        return cls(modulus, gain % modulus, carry % modulus)

    def apply(self, source: int) -> int:
        value = self.gain * source + self.carry
        return value if self.modulus is None else value % self.modulus

    def then(self, following: AffinePortAction) -> AffinePortAction:
        """Apply the following response after this one."""
        if self.modulus != following.modulus:
            raise ValueError("affine ports use different coefficient rings")
        gain = following.gain * self.gain
        carry = following.gain * self.carry + following.carry
        if self.modulus is None:
            return AffinePortAction(None, gain, carry)
        return AffinePortAction.reduced(self.modulus, gain, carry)


@lru_cache(maxsize=256, typed=True)
def canonical_radix_digit_response(
    radix: int, gain: int, carry: int
) -> tuple[int, ...]:
    """Return a reduced affine response row without source authority."""
    if (
        type(radix) is not int
        or not 2 <= radix <= 256
        or type(gain) is not int
        or not 0 <= gain < radix
        or type(carry) is not int
        or not 0 <= carry < radix
    ):
        raise ValueError("digit response requires reduced affine coefficients")
    return tuple((gain * digit + carry) % radix for digit in range(radix))
