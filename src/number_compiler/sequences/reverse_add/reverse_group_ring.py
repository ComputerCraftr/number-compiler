"""Exact variable-width (I + R) decimal carry correction for reverse/add.

The raw Q19 coefficient word S is palindromic.  Normalizing it produces
Y = S + (z - 10) H.  Its *next* unnormalized reverse/add word is

    (I + R_W)Y = (1 + z**birth) S + (I + R_W)(z - 10) H,

where W = len(S) + birth and birth is the terminal outgoing carry.

This is a coefficient oracle, not a claim that a future physical carry tape
will repeat.  It is deliberately independent of Q19 occurrence identities,
scalar source integers, and any assumed future border periods.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class ReverseAddGroupRingCarry:
    """One physical raw-to-next-raw source action over the reversal involution.

    ``symbol_at`` evaluates S_i and ``carry_at`` evaluates the normalization
    carry c_i at the boundary immediately before raw coefficient i, with c_0=0.
    Both functions may be sourced from a single compact carry/SLP port fold.
    """

    width: int
    birth: int

    def __post_init__(self) -> None:
        if type(self.width) is not int or self.width < 1:
            raise ValueError("reverse/add group-ring action requires positive width")
        if type(self.birth) is not int or self.birth not in (0, 1):
            raise ValueError("reverse/add group-ring birth must be Boolean")

    @property
    def next_raw_width(self) -> int:
        return self.width + self.birth

    def symbol_offsets(self, index: int) -> tuple[int, ...]:
        self._validate_index(index)
        if self.birth:
            if index == 0 or index == self.width:
                return (0,)
            return index - 1, index
        return (index,)

    def carry_offsets(self, index: int) -> tuple[int, ...]:
        """Boundaries needed to apply both D H and its reflection."""
        self._validate_index(index)
        if self.birth:
            if index == 0 or index == self.width:
                return (1,)
            return index, self.width - index, index + 1, self.width - index + 1
        return index, self.width - 1 - index, index + 1, self.width - index

    def _validate_index(self, index: int) -> None:
        if type(index) is not int or not 0 <= index < self.next_raw_width:
            raise IndexError(index)

    @staticmethod
    def _validate_residue_projection(
        normalized_mod: int, reflected_mod: int, birth: int, modulus: int
    ) -> int:
        if type(birth) is not int or birth not in (0, 1):
            raise ValueError("birth must be Boolean")
        if type(normalized_mod) is not int or type(reflected_mod) is not int:
            raise TypeError("group-ring residues must be exact integers")
        if type(modulus) is not int or modulus < 2:
            raise ValueError("modulus must be >= 2")
        return 99 * modulus

    def coefficient(
        self,
        index: int,
        *,
        symbol_at: Callable[[int], int],
        carry_at: Callable[[int], int],
    ) -> int:
        """Evaluate the exact raw next coefficient without normalizing Y."""
        self._validate_index(index)
        w = self.width
        if self.birth:
            if index in (0, w):
                return symbol_at(0) + 1 - 10 * carry_at(1)
            return (
                symbol_at(index - 1)
                + symbol_at(index)
                + carry_at(index)
                + carry_at(w - index)
                - 10 * (carry_at(index + 1) + carry_at(w - index + 1))
            )
        return (
            2 * symbol_at(index)
            + carry_at(index)
            + carry_at(w - 1 - index)
            - 10 * (carry_at(index + 1) + carry_at(w - index))
        )

    @staticmethod
    def reflected_correction_mod(
        normalized_mod: int, reflected_mod: int, birth: int, modulus: int
    ) -> int:
        """Return -99 K mod modulus without dividing by 99 or by 10.

        For the complete physical carry word,
           rev10(Y) = 10**birth * Y - 99 K.
        This works over non-coprime rings too. To recover K modulo m,
        evaluate the correction modulo 99*m and then divide by 99.
        """
        ReverseAddGroupRingCarry._validate_residue_projection(
            normalized_mod, reflected_mod, birth, modulus
        )
        return (reflected_mod - (10 if birth else 1) * normalized_mod) % modulus

    @staticmethod
    def carry_weight_mod(
        normalized_mod: int, reflected_mod: int, birth: int, modulus: int
    ) -> int:
        """Recover the reflected carry K modulo m from residues modulo 99m."""
        big = ReverseAddGroupRingCarry._validate_residue_projection(
            normalized_mod, reflected_mod, birth, modulus
        )
        defect = ((10 if birth else 1) * normalized_mod - reflected_mod) % big
        if defect % 99:
            raise ValueError("reflected carry defect is not divisible by 99")
        return defect // 99


__all__ = ["ReverseAddGroupRingCarry"]
