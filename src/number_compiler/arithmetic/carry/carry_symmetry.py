"""Shared oriented carry-action quotients for reverse/add and Collatz."""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Sequence

from number_compiler.arithmetic.automata.symmetry_powering import (
    ActionTransform,
    FiniteKernel,
    OrientedActionRef,
    OrientedFiniteActionArena,
)
from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn, value_carry_fn


@dataclass(frozen=True, slots=True)
class CarryWordAction:
    ref: OrientedActionRef
    length: int

    @property
    def action_id(self) -> int:
        return self.ref.action_id

    @property
    def transform(self) -> ActionTransform:
        return self.ref.transform


@lru_cache(maxsize=None)
def reverse_add_carry_kernel(base: int = 10) -> FiniteKernel:
    base = int(base)
    if base < 2:
        raise ValueError(base)
    blank = 2 * base - 1

    def transition(carry: int, symbol: int) -> int:
        carry, symbol = int(carry), int(symbol)
        if symbol == blank:
            return carry
        return apply_carry_fn(value_carry_fn(symbol, base), carry)

    symbol_conjugate = tuple(
        blank if symbol == blank else 2 * (base - 1) - symbol
        for symbol in range(blank + 1)
    )
    return FiniteKernel(
        2,
        blank + 1,
        transition,
        state_conjugate=(1, 0),
        symbol_conjugate=symbol_conjugate,
        name=f"reverse-add-carry-b{base}",
    )


@lru_cache(maxsize=None)
def collatz_mul3_carry_kernel(base: int = 10) -> FiniteKernel:
    base = int(base)
    if base < 3:
        raise ValueError(base)

    def transition(carry: int, digit: int) -> int:
        carry, digit = int(carry), int(digit)
        out = (3 * digit + carry) // base
        if not 0 <= out <= 2:
            raise ValueError((base, carry, digit, out))
        return out

    return FiniteKernel(
        3,
        base,
        transition,
        state_conjugate=(2, 1, 0),
        symbol_conjugate=tuple(base - 1 - d for d in range(base)),
        name=f"collatz-mul3-carry-b{base}",
    )


def reverse_add_carry_action_arena(base: int = 10) -> OrientedFiniteActionArena:
    """Create an independently owned arena over the shared immutable kernel."""
    return OrientedFiniteActionArena(reverse_add_carry_kernel(int(base)))


def collatz_mul3_carry_action_arena(base: int = 10) -> OrientedFiniteActionArena:
    """Create an independently owned arena over the shared immutable kernel."""
    return OrientedFiniteActionArena(collatz_mul3_carry_kernel(int(base)))


def _word_action(
    values: Sequence[int],
    arena: OrientedFiniteActionArena,
) -> CarryWordAction:
    values = tuple(map(int, values))
    if not values:
        raise ValueError("empty carry word")
    current = arena.leaf(values[0])
    for symbol in values[1:]:
        current = arena.compose(current, arena.leaf(symbol))
    return CarryWordAction(current, len(values))


def reverse_add_carry_word_action(
    values: Sequence[int],
    *,
    base: int = 10,
    arena: OrientedFiniteActionArena,
) -> CarryWordAction:
    if arena.kernel != reverse_add_carry_kernel(base):
        raise ValueError("carry word arena has a different finite kernel")
    return _word_action(values, arena)


def collatz_mul3_carry_word_action(
    digits: Sequence[int],
    *,
    base: int = 10,
    arena: OrientedFiniteActionArena,
) -> CarryWordAction:
    if arena.kernel != collatz_mul3_carry_kernel(base):
        raise ValueError("carry word arena has a different finite kernel")
    return _word_action(digits, arena)


__all__ = [
    "CarryWordAction",
    "reverse_add_carry_kernel",
    "collatz_mul3_carry_kernel",
    "reverse_add_carry_action_arena",
    "collatz_mul3_carry_action_arena",
    "reverse_add_carry_word_action",
    "collatz_mul3_carry_word_action",
]
