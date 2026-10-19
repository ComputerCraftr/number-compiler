"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from tests.support.diamond_runtime import build as build_runtime

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_execution_adapter import (
        FamilyTileHooks,
    )


def build(
    effect: BlockEffect,
    source: tuple[int, ...],
    length: int,
    steps: int,
    *,
    family_hooks: FamilyTileHooks | None = None,
) -> DiamondApplication:
    runtime, root = build_runtime(
        effect, source, length, steps, family_hooks=family_hooks
    )
    return DiamondApplication(runtime, root)


def oracle(
    effect: BlockEffect, source: tuple[int, ...], length: int, steps: int
) -> list[int]:
    word = list(source) + [effect.blank] * (length - len(source))
    for _ in range(steps):
        left, right = (
            [effect.initial(BoundarySide.LEFT)],
            [effect.initial(BoundarySide.RIGHT)],
        )
        for symbol in word:
            left.append(effect.advance(BoundarySide.LEFT, left[-1], symbol))
        for symbol in reversed(word):
            right.append(effect.advance(BoundarySide.RIGHT, right[-1], symbol))
        right.reverse()
        word = [
            effect.emit(left[i], symbol, right[i + 1]) for i, symbol in enumerate(word)
        ]
    return word


def bounded_case(
    effect: BlockEffect,
    steps: int,
    *,
    family_hooks: FamilyTileHooks | None = None,
) -> tuple[DiamondApplication, list[int]]:
    source = (1, 0, 1) if effect.base == 2 else (2, 4, 2)
    return (
        build(effect, source, 8, steps, family_hooks=family_hooks),
        oracle(effect, source, 8, steps),
    )
