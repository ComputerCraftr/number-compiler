"""Finite-state producer for the exact fixed-width 2rev10 T² law."""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import cast

from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.resources.ledger import OwnedMemo


class _TwoStepLeftDFA:
    start = 0

    @staticmethod
    def step(state: int, symbol: int) -> int | None:
        if state not in (0, 1) or not 0 <= symbol <= 9:
            return None
        return int(symbol >= 5)


class _TwoStepRightDFA:
    start = 10

    @staticmethod
    def step(state: int, symbol: int) -> int | None:
        if state not in (0, 1, 2, 3, 4, 10) or not 0 <= symbol <= 9:
            return None
        return symbol % 5


class DoubleReverseTwoStepMachine:
    """T² local law from the exact carry/residue recurrence."""

    __slots__ = ("left", "right")

    def __init__(self) -> None:
        self.left = _TwoStepLeftDFA()
        self.right = _TwoStepRightDFA()

    @staticmethod
    def _phi(residue: int, high: int) -> int:
        return int(residue >= 3 or (residue == 2 and high == 1))

    @classmethod
    def emit(
        cls, high_left: int, symbol: int, residue_right: int
    ) -> tuple[int, ...] | None:
        if (
            high_left not in (0, 1)
            or not 0 <= symbol <= 9
            or residue_right not in (0, 1, 2, 3, 4, 10)
        ):
            return None
        high = int(symbol >= 5)
        residue = symbol % 5
        carry_in = 0 if residue_right == 10 else cls._phi(residue_right, high)
        next_residue = (2 * residue + high_left) % 5
        next_high = cls._phi(next_residue, carry_in)
        output_residue = (2 * next_residue + carry_in) % 5
        return (5 * next_high + output_residue,)


def attach_projector_memos(
    projector: BimachineSLPProjector,
    memos: tuple[OwnedMemo[object, object], ...],
) -> None:
    if len(memos) != 5:
        raise ValueError("bimachine projector requires five owned memos")
    projector._fwd = cast(MutableMapping[tuple[int, int], int | None], memos[0])
    projector._rev = cast(MutableMapping[tuple[int, int], int | None], memos[1])
    projector._block = cast(MutableMapping[tuple[int, int, int], int], memos[2])
    projector._fwd_power = cast(
        MutableMapping[tuple[int, int, int], int | None], memos[3]
    )
    projector._rev_power = cast(
        MutableMapping[tuple[int, int, int], int | None], memos[4]
    )
