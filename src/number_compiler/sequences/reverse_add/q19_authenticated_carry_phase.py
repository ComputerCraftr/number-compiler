"""Lossless *guarded* ×5 carry-sheet coordinate for decimal Q19 sources.

A carry symbol ``c[j] = floor(d[j]/2)`` does not determine a decimal digit
without its parity bit.  An independently authenticated 2-adic residue does:

    R[0] = X mod 2**k
    p[j] = ((R[j] - 2*c[j]*10**j) // 2**j) & 1
    R[j+1] = R[j] - (2*c[j] + p[j])*10**j.

The map (carry sheet, X mod 2**k) <-> X mod 10**k is a bijection.  This
also holds for *arbitrary* decimal sources, unlike the carry-only isometry
of authenticated powers of five, which has a special orbit restriction.

This decoder is intended for externally supplied authenticated carry sheets.
Do not produce a carry sheet from a known decimal source and immediately
invert it on the default path: that would be redundant work.  In particular,
no claim about a physical reverse/add temporal period follows from it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .q19_repeat_port import Q19RepeatPortState
    from .temporal_boolean_ring_2_11 import Mixed211Phase


def _is_tuple(value: object) -> bool:
    return isinstance(value, tuple)


@dataclass(frozen=True, slots=True, init=False)
class AuthenticatedFiveCarryWindow:
    """A single ×5 carry sheet plus its certified dyadic source coordinate.

    The carry planes contain the 3 binary bits of each 0..4 symbol.  The
    inverse emits the source's parity plane, so its decimal BCD representation
    is simply ``(parity, carry_bit0, carry_bit1, carry_bit2)``.  All planes
    remain bit-packed and no full decimal digit tuple is materialized.
    """

    width: int
    carries: tuple[int, int, int]
    dyadic_source: int
    parity_plane: int

    @classmethod
    def _from_verified(
        cls,
        width: int,
        carries: tuple[int, int, int],
        dyadic_source: int,
        parity_plane: int,
    ) -> AuthenticatedFiveCarryWindow:
        """Private construction only after exact triangular verification."""
        state = object.__new__(cls)
        object.__setattr__(state, "width", width)
        object.__setattr__(state, "carries", carries)
        object.__setattr__(state, "dyadic_source", dyadic_source)
        object.__setattr__(state, "parity_plane", parity_plane)
        return state

    @classmethod
    def from_carries(
        cls, carries: tuple[int, int, int], width: int, dyadic_source: int
    ) -> AuthenticatedFiveCarryWindow:
        if type(width) is not int or width <= 0:
            raise ValueError("positive decimal band width required")
        mask = (1 << width) - 1
        if (
            not _is_tuple(carries)
            or len(carries) != 3
            or any(type(x) is not int or x < 0 or x & ~mask for x in carries)
        ):
            raise ValueError("three bounded carry bitplanes required")
        c0, c1, c2 = carries
        if c2 & (c0 | c1):
            raise ValueError("×5 outgoing carry must be in 0..4")
        if type(dyadic_source) is not int or not 0 <= dyadic_source <= mask:
            raise ValueError("dyadic residue must be reduced modulo 2**width")
        remainder = dyadic_source
        power10 = 1
        parity = 0
        for j in range(width):
            c = ((c0 >> j) & 1) + 2 * ((c1 >> j) & 1) + 4 * ((c2 >> j) & 1)
            remainder -= 2 * c * power10
            p = (remainder >> j) & 1
            parity |= p << j
            remainder -= p * power10
            power10 *= 10
        # By triangular inversion, the reconstructed integer has precisely
        # the supplied binary residue; this assertion also checks the code.
        if remainder & mask:
            raise AssertionError("dyadic carry-sheet inverse left a binary defect")
        return cls._from_verified(width, carries, dyadic_source, parity)

    @classmethod
    def from_mixed211_source(
        cls, seed: int, phase: Mixed211Phase, carries: tuple[int, int, int]
    ) -> AuthenticatedFiveCarryWindow:
        """Authenticate both 2-adic and 5-adic coordinates before reuse.

        Matching only the ×5 carries is UNSAFE.  The homogeneous source
        phase proves the dyadic residue and the 5-adic multiplier; together
        they authenticate the complete decimal band.  This method refuses
        foreign sheets and never guesses a phase from ambiguous carries.
        """
        from .temporal_boolean_ring_2_11 import Mixed211Phase

        if type(seed) is not int or seed < 0 or type(phase) is not Mixed211Phase:
            raise ValueError("nonnegative seed and exact mixed phase required")
        width = phase.k
        modulus2 = 1 << width
        if phase.q_cap == width:
            r2 = 0
        else:
            r2 = (
                (1 << phase.q_cap) * pow(11, phase.g2, 1 << (width - phase.q_cap))
            ) % modulus2
        r2 = (seed * r2) % modulus2
        window = cls.from_carries(carries, width, r2)
        modulus5 = int(5**width)
        r5 = seed * pow(2, phase.q4, modulus5) * pow(16, phase.t5, modulus5)
        if window.residue() % modulus5 != r5 % modulus5:
            raise ValueError(
                "carry sheet does not belong to the authenticated 2^q11^g phase"
            )
        return window

    @property
    def bcd_planes(self) -> tuple[int, int, int, int]:
        return (self.parity_plane, *self.carries)

    def residue(self) -> int:
        """Decode only on explicit numeric demand, not during local masks."""
        c0, c1, c2 = self.carries
        value = 0
        power10 = 1
        for j in range(self.width):
            carry = ((c0 >> j) & 1) + 2 * ((c1 >> j) & 1) + 4 * ((c2 >> j) & 1)
            value += (2 * carry + ((self.parity_plane >> j) & 1)) * power10
            power10 *= 10
        return value

    def same_source_mask(self, after: AuthenticatedFiveCarryWindow) -> int:
        """Exact unchanged-digit mask for two separately authenticated rows.

        This is NOT an assertion that the two rows are consecutive physical
        reverse/add generations.  It is reusable only within an owner-issued
        ordered future action that checks the source seam.
        """
        if type(after) is not type(self) or after.width != self.width:
            raise ValueError("same-digit comparison requires matching precision")
        differences = self.parity_plane ^ after.parity_plane
        for left, right in zip(self.carries, after.carries, strict=True):
            differences |= left ^ right
        return ((1 << self.width) - 1) & ~differences

    def q19_repeat_state(self) -> Q19RepeatPortState:
        """Construct Q19's actual source ports from bitplanes, not digit tuples."""
        from .q19_repeat_port import Q19RepeatPortState

        nonzero = 0
        for bits in self.bcd_planes:
            nonzero |= bits
        physical_width = nonzero.bit_length()
        if not physical_width:
            raise ValueError("physical Q19 input must be positive")
        mask = (1 << physical_width) - 1
        p0, p1, p2, p3 = self.bcd_planes
        planes = (p0 & mask, p1 & mask, p2 & mask, p3 & mask)
        return Q19RepeatPortState.from_bcd_planes(planes, physical_width)


__all__ = ["AuthenticatedFiveCarryWindow"]
