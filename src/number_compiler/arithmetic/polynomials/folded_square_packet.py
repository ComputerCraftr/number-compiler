"""Two demanded folded-square residues, without a complete convolution.

This arithmetic observer does not certify an etale support or primality bit.
Its generic mirror-pair extraction has linear work in the coefficient width.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class FoldedSquarePacket:
    r1_mod4: int
    r2_mod8: int

    def __post_init__(self) -> None:
        if type(self.r1_mod4) is not int or not 0 <= self.r1_mod4 < 4:
            raise ValueError("first folded coefficient must be reduced modulo four")
        if type(self.r2_mod8) is not int or not 0 <= self.r2_mod8 < 8:
            raise ValueError("second folded coefficient must be reduced modulo eight")

    @property
    def vanishes(self) -> bool:
        """A residue predicate; no support/primality admission is implied."""
        return self.r1_mod4 == 0 and self.r2_mod8 == 0

    @property
    def canonical_key(self) -> tuple[int, int]:
        return self.r1_mod4, self.r2_mod8


@dataclass(frozen=True, slots=True)
class FoldedSquareProjection:
    packet: FoldedSquarePacket
    coefficient_reads: int
    pair_visits: int
    scalar_products: int

    @property
    def r1_mod4(self) -> int:
        return self.packet.r1_mod4

    @property
    def r2_mod8(self) -> int:
        return self.packet.r2_mod8

    @property
    def vanishes(self) -> bool:
        return self.packet.vanishes


def folded_square_packet(
    coefficients: Sequence[int], *, sign: int
) -> FoldedSquareProjection:
    """Project ``X**2 mod (z**w-sign)`` at coefficients one and two.

    Inputs are exact coefficients of degree less than ``w``, with ``w>=3``.
    Each unordered mirror pair is multiplied once; its off-diagonal partner
    contributes the same product. All arithmetic is reduced modulo four/eight
    before accumulation. No square/deck representative change is permitted:
    this observer concerns this polynomial, before digit normalization.
    """
    if type(sign) is not int or sign not in (-1, 1):
        raise ValueError("the fold sign must be -1 or +1")
    width = len(coefficients)
    if width < 3:
        raise ValueError("two nonconstant folded coefficients require width >= 3")
    for value in coefficients:
        if type(value) is not int:
            raise TypeError("folded-square inputs must be exact integer coefficients")
    reads = width
    visits = products = 0
    residues: list[int] = []
    for position, modulus in ((1, 4), (2, 8)):
        residue = 0
        for degree, weight in ((position, 1), (width + position, sign)):
            low = max(0, degree - width + 1)
            high = min(width - 1, degree // 2)
            for left in range(low, high + 1):
                right = degree - left
                a = coefficients[left] % modulus
                b = coefficients[right] % modulus
                reads += 2
                visits += 1
                if a and b:
                    product = a * b
                    products += 1
                    multiplicity = 1 if left == right else 2
                    residue = (residue + weight * multiplicity * product) % modulus
        residues.append(residue)
    return FoldedSquareProjection(
        FoldedSquarePacket(*residues), reads, visits, products
    )


__all__ = ["FoldedSquarePacket", "FoldedSquareProjection", "folded_square_packet"]
