"""Immutable decimal pair-step law and composable Q19 word summaries.

This module owns the algebra used by the ledgered output owner to summarize
the forward, reverse, and punctured views of its SLP words.  It contains no
source occurrence or resource ownership state.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from functools import cache

from number_compiler.arithmetic.automata.transducer import (
    build_pair_step_bimachine,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power

_NEUTRAL = 0
_LOWER = -1
Q19_UPPER = 1


@dataclass(frozen=True, slots=True)
class FrozenPairDFA:
    alphabet: tuple[int, ...]
    start: int
    trans: tuple[tuple[int | None, ...], ...]
    states: tuple[int, ...]
    right: bool

    def step(self, state: int, symbol: int) -> int | None:
        if not 0 <= state < len(self.trans) or not 0 <= symbol < len(self.alphabet):
            return None
        return self.trans[state][symbol]


@dataclass(frozen=True, slots=True)
class FrozenPairStepLaw:
    base: int
    alphabet: tuple[int, ...]
    left: FrozenPairDFA
    right: FrozenPairDFA
    resolver: Callable[[int, int, int], tuple[int, ...] | None]

    def emit(self, left: int, symbol: int, right: int) -> tuple[int, ...] | None:
        return self.resolver(int(left), int(symbol), int(right))


@cache
def pair_step_law() -> FrozenPairStepLaw:
    """One immutable finite decimal law shared by request-local owners."""
    machine = build_pair_step_bimachine(10)
    machine.cache_enabled = False
    machine.clear_output_cache()
    left = FrozenPairDFA(
        machine.left.alphabet,
        machine.left.start,
        tuple(
            tuple(machine.left.step(state, symbol) for symbol in machine.alphabet)
            for state in machine.left.states
        ),
        tuple(machine.left.states),
        machine.left.right,
    )
    right = FrozenPairDFA(
        machine.right.alphabet,
        machine.right.start,
        tuple(
            tuple(machine.right.step(state, symbol) for symbol in machine.alphabet)
            for state in machine.right.states
        ),
        tuple(machine.right.states),
        machine.right.right,
    )
    return FrozenPairStepLaw(
        machine.base,
        tuple(machine.alphabet),
        left,
        right,
        machine.resolver,
    )


@dataclass(frozen=True, slots=True)
class Q19Summary:
    length: int
    domain: int
    f9: int

    @classmethod
    def identity(cls) -> Q19Summary:
        return cls(0, _NEUTRAL, 0)

    @classmethod
    def atom(cls, value: int) -> Q19Summary:
        if type(value) is not int or not 0 <= value <= 18:
            raise ValueError("decimal pair symbols must lie in 0..18")
        defect = value - 9
        return cls(
            1, _LOWER if defect < 0 else Q19_UPPER if defect > 0 else 0, defect % 9
        )

    def then(self, right: Q19Summary) -> Q19Summary:
        if type(right) is not Q19Summary:
            raise TypeError("Q19 composition requires another summary")
        if right.length == 0:
            return self
        if self.length == 0:
            return right
        domain = right.domain if right.domain != _NEUTRAL else self.domain
        phase = (self.f9 + pow(2, self.length, 9) * right.f9) % 9
        return Q19Summary(self.length + right.length, domain, phase)

    def repeat(self, count: int) -> Q19Summary:
        if type(count) is not int or count < 0:
            raise ValueError("Q19 repetition count must be nonnegative")
        return binary_power(
            self,
            count,
            identity=Q19Summary.identity(),
            compose=lambda first, second: first.then(second),
        ).value

    def validate_symmetric(self) -> None:
        if self.length < 1:
            raise ValueError("pair output must be nonempty")
        if self.length & 1:
            if self.domain == _NEUTRAL:
                raise ValueError("odd symmetric pair output has a neutral center")
        elif self.f9 % 3:
            raise ValueError("even symmetric pair output has an invalid F9 phase")


@dataclass(frozen=True, slots=True)
class WordSummary:
    symbols: int
    forward: Q19Summary
    reverse: Q19Summary
    prefix_forward: Q19Summary
    prefix_reverse: Q19Summary
    first_symbol: int | None
    last_symbol: int | None
    runs: int
