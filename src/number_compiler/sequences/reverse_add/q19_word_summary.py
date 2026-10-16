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
_UPPER = 1


@dataclass(frozen=True, slots=True)
class _FrozenPairDFA:
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
class _FrozenPairStepLaw:
    base: int
    alphabet: tuple[int, ...]
    left: _FrozenPairDFA
    right: _FrozenPairDFA
    resolver: Callable[[int, int, int], tuple[int, ...] | None]

    def emit(self, left: int, symbol: int, right: int) -> tuple[int, ...] | None:
        return self.resolver(int(left), int(symbol), int(right))


@cache
def _pair_step_law() -> _FrozenPairStepLaw:
    """One immutable finite decimal law shared by request-local owners."""
    machine = build_pair_step_bimachine(10)
    machine.cache_enabled = False
    machine.clear_output_cache()
    left = _FrozenPairDFA(
        machine.left.alphabet,
        machine.left.start,
        tuple(
            tuple(machine.left.step(state, symbol) for symbol in machine.alphabet)
            for state in machine.left.states
        ),
        tuple(machine.left.states),
        machine.left.right,
    )
    right = _FrozenPairDFA(
        machine.right.alphabet,
        machine.right.start,
        tuple(
            tuple(machine.right.step(state, symbol) for symbol in machine.alphabet)
            for state in machine.right.states
        ),
        tuple(machine.right.states),
        machine.right.right,
    )
    return _FrozenPairStepLaw(
        machine.base,
        tuple(machine.alphabet),
        left,
        right,
        machine.resolver,
    )


@dataclass(frozen=True, slots=True)
class _Q19:
    length: int
    domain: int
    f9: int

    @classmethod
    def identity(cls) -> _Q19:
        return cls(0, _NEUTRAL, 0)

    @classmethod
    def atom(cls, value: int) -> _Q19:
        if type(value) is not int or not 0 <= value <= 18:
            raise ValueError("decimal pair symbols must lie in 0..18")
        defect = value - 9
        return cls(1, _LOWER if defect < 0 else _UPPER if defect > 0 else 0, defect % 9)

    def then(self, right: _Q19) -> _Q19:
        if type(right) is not _Q19:
            raise TypeError("Q19 composition requires another summary")
        if right.length == 0:
            return self
        if self.length == 0:
            return right
        domain = right.domain if right.domain != _NEUTRAL else self.domain
        phase = (self.f9 + pow(2, self.length, 9) * right.f9) % 9
        return _Q19(self.length + right.length, domain, phase)

    def repeat(self, count: int) -> _Q19:
        if type(count) is not int or count < 0:
            raise ValueError("Q19 repetition count must be nonnegative")
        return binary_power(
            self,
            count,
            identity=_Q19.identity(),
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
class _WordSummary:
    symbols: int
    forward: _Q19
    reverse: _Q19
    prefix_forward: _Q19
    prefix_reverse: _Q19
    first_symbol: int | None
    last_symbol: int | None
    runs: int
