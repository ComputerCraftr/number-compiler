"""Finite radix-64 mirror correlation for a demanded fifth folded coefficient.

Only the additive residue is an action ID. Alignment, the source occurrence,
and the low boundary port are supplied by the caller, never retained in it.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from enum import IntEnum


class MirrorCorrActionID(IntEnum):
    """The sixteen canonical translations of a modulo-sixteen accumulator."""

    ZERO = 0
    ONE = 1
    TWO = 2
    THREE = 3
    FOUR = 4
    FIVE = 5
    SIX = 6
    SEVEN = 7
    EIGHT = 8
    NINE = 9
    TEN = 10
    ELEVEN = 11
    TWELVE = 12
    THIRTEEN = 13
    FOURTEEN = 14
    FIFTEEN = 15

    @property
    def residue(self) -> int:
        return int(self)

    def then(self, other: MirrorCorrActionID) -> MirrorCorrActionID:
        if type(other) is not MirrorCorrActionID:
            raise TypeError("mirror composition requires a mirror action ID")
        return MirrorCorrActionID((int(self) + int(other)) % 16)

    def apply(self, incoming: int) -> int:
        if type(incoming) is not int or not 0 <= incoming < 16:
            raise ValueError("mirror accumulator must be reduced modulo sixteen")
        return (incoming + int(self)) % 16

    def power(self, copies: int) -> MirrorCorrActionID:
        """Repeat an already known spatial action without expanding its leaves."""
        if type(copies) is not int or copies < 0:
            raise ValueError("mirror repetition requires a nonnegative exact count")
        return MirrorCorrActionID((int(self) * (copies % 16)) % 16)


def mirror_leaf_action(left: int, right: int) -> MirrorCorrActionID:
    """Consume two aligned six-bit words into one of seven leaf actions."""
    if any(type(word) is not int or not 0 <= word < 64 for word in (left, right)):
        raise ValueError("mirror leaves require two unsigned radix-64 words")
    return MirrorCorrActionID((left & right).bit_count())


def compose_mirror_pairs(pairs: Iterable[tuple[int, int]]) -> MirrorCorrActionID:
    """Consume an already aligned pair stream without retaining its leaves."""
    action = MirrorCorrActionID.ZERO
    for left, right in pairs:
        action = action.then(mirror_leaf_action(left, right))
    return action


def folded_mirror_residue(
    low: int, mirror: MirrorCorrActionID, *, sign: int
) -> int:
    """Consume the fold geometry and low boundary port after mirror reduction."""
    if type(low) is not int or not 0 <= low < 16:
        raise ValueError("the low coefficient port must be reduced modulo sixteen")
    if type(mirror) is not MirrorCorrActionID:
        raise TypeError("the wrap contribution requires a mirror action ID")
    if type(sign) is not int or sign not in (-1, 1):
        raise ValueError("the fold sign must be -1 or +1")
    return (low + sign * int(mirror)) % 16


@dataclass(frozen=True, slots=True)
class FoldedFifthProjection:
    residue: int
    low_residue: int
    mirror_action: MirrorCorrActionID
    coefficient_reads: int
    leaf_pairs: int

    @property
    def vanishes(self) -> bool:
        """Zero is an observation, not an unrestricted support certificate."""
        return self.residue == 0


def _reflected_pairs(coefficients: Sequence[int]) -> Iterator[tuple[int, int]]:
    width = len(coefficients)
    for start in range(0, width - 6, 6):
        left = right = 0
        for offset in range(min(6, width - 6 - start)):
            left |= coefficients[start + offset + 6] << offset
            right |= coefficients[width - 1 - start - offset] << offset
        yield left, right


def folded_fifth_residue(
    coefficients: Sequence[int], *, sign: int
) -> FoldedFifthProjection:
    """Lower a binary polynomial into a boundary port and reflected leaf pairs.

    For ``w>=6``, the wrap term is the dot product of ``x[u+6]`` and
    ``x[w-1-u]`` over ``u<w-6``. Both words in a last partial leaf are
    zero-padded in the same positions. Dense source validation and lowering
    remain linear; the action itself has only sixteen possible identities.
    """
    if type(sign) is not int or sign not in (-1, 1):
        raise ValueError("the fold sign must be -1 or +1")
    width = len(coefficients)
    if width < 6:
        raise ValueError("coefficient five requires fold width >= 6")
    low = reflected_low = 0
    for index, bit in enumerate(coefficients):
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("the mirror observer requires binary source coefficients")
        if index < 6:
            low |= bit << index
            reflected_low |= bit << (5 - index)
    low_residue = int(mirror_leaf_action(low, reflected_low))
    mirror = compose_mirror_pairs(_reflected_pairs(coefficients))
    # Exactly one validation read per source bit and two reads per reflected
    # position; the low port is packed during validation, without rereading.
    reads = width + 2 * (width - 6)
    leaves = 1 + (width - 6 + 5) // 6
    return FoldedFifthProjection(
        folded_mirror_residue(low_residue, mirror, sign=sign),
        low_residue,
        mirror,
        reads,
        leaves,
    )


__all__ = [
    "FoldedFifthProjection", "MirrorCorrActionID", "compose_mirror_pairs",
    "folded_fifth_residue", "folded_mirror_residue", "mirror_leaf_action",
]
