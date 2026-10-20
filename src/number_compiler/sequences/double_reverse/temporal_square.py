"""Finite-state producer for the exact fixed-width 2rev10 T² law."""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import cast

from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.double_reverse.stencil_moore import (
    stencil_from_ports,
)


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
        right_f5 = 0 if residue_right == 10 else residue_right
        return (stencil_from_ports(high_left, symbol, right_f5),)


def attach_projector_memos(
    projector: BimachineSLPProjector,
    memos: tuple[OwnedMemo[object, object], ...],
) -> None:
    if len(memos) != 5:
        raise ValueError("bimachine projector requires five owned memos")
    projector.bind_cache_stores(
        forward=cast(MutableMapping[tuple[int, int], int | None], memos[0]),
        reverse=cast(MutableMapping[tuple[int, int], int | None], memos[1]),
        block=cast(MutableMapping[tuple[int, int, int], int], memos[2]),
        forward_power=cast(MutableMapping[tuple[int, int, int], int | None], memos[3]),
        reverse_power=cast(MutableMapping[tuple[int, int, int], int | None], memos[4]),
    )
