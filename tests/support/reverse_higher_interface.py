"""Reverse higher interface with one canonical implementation owner."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect


def direct_step(word: tuple[int, ...], base: int) -> tuple[int, ...]:
    effect = BaseBlockEffect(base)
    left: list[object] = []
    state = effect.initial(BoundarySide.LEFT)
    for symbol in word:
        left.append(state)
        state = effect.advance(BoundarySide.LEFT, state, symbol)
    right: list[object] = [effect.initial(BoundarySide.RIGHT)] * len(word)
    state = effect.initial(BoundarySide.RIGHT)
    for index in range(len(word) - 1, -1, -1):
        right[index] = state
        state = effect.advance(BoundarySide.RIGHT, state, word[index])
    return tuple(
        effect.emit(left[index], symbol, right[index])
        for index, symbol in enumerate(word)
    )
