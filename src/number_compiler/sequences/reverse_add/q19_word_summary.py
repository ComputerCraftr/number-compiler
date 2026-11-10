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
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    decimal_pair_partition,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

_NEUTRAL = 0
Q19_LOWER = -1
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
            1,
            Q19_LOWER if defect < 0 else Q19_UPPER if defect > 0 else _NEUTRAL,
            defect % 9,
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


@dataclass(frozen=True, slots=True)
class Q19CarryPhi6Summary:
    """Demanded spatial carry response, with both forward Phi6 roots.

    This sidecar is never built by the ordinary Q19 output fold. Its carry
    effect is the canonical three-element carry monoid, in LSD-to-MSD order.
    """

    length: int
    effect: CarryFn
    bands3: tuple[int, int, int, int, int]
    carry3: tuple[int, int]
    carry5: tuple[int, int]

    @classmethod
    def identity(cls) -> Q19CarryPhi6Summary:
        return cls(0, CarryFn.ID, (0, 0, 0, 0, 0), (0, 0), (0, 0))

    @classmethod
    def atom(cls, symbol: int) -> Q19CarryPhi6Summary:
        effect = value_carry_fn(symbol, 10)
        outcomes = (apply_carry_fn(effect, 0), apply_carry_fn(effect, 1))
        return cls(1, effect, decimal_pair_partition(symbol).masks, outcomes, outcomes)

    def carry_exit(self, incoming: int) -> int:
        return apply_carry_fn(self.effect, incoming)

    def then(
        self, right: Q19CarryPhi6Summary, *, ledger: ResourceLedger | None = None
    ) -> Q19CarryPhi6Summary:
        if type(right) is not Q19CarryPhi6Summary:
            raise TypeError("Phi6 carry composition requires another summary")
        if not self.length:
            return right
        if not right.length:
            return self
        ingress = (self.carry_exit(0), self.carry_exit(1))
        phase3 = pow(3, self.length % 6, 7)
        phase5 = pow(5, self.length % 6, 7)
        if ledger is not None:
            ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_COMPOSITIONS)
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OPERAND_BITS,
                self.length.bit_length()
                + right.length.bit_length()
                + sum(
                    part.bit_length()
                    for part in (
                        *self.bands3,
                        *right.bands3,
                        *self.carry3,
                        *self.carry5,
                        *right.carry3,
                        *right.carry5,
                    )
                ),
            )
        bands = tuple(
            (self.bands3[index] + phase3 * right.bands3[index]) % 7
            for index in range(5)
        )
        if len(bands) != 5:
            raise AssertionError("five-band Q19 alphabet changed")
        return Q19CarryPhi6Summary(
            self.length + right.length,
            compose_carry_fn(right.effect, self.effect),
            (bands[0], bands[1], bands[2], bands[3], bands[4]),
            (
                (self.carry3[0] + phase3 * right.carry3[ingress[0]]) % 7,
                (self.carry3[1] + phase3 * right.carry3[ingress[1]]) % 7,
            ),
            (
                (self.carry5[0] + phase5 * right.carry5[ingress[0]]) % 7,
                (self.carry5[1] + phase5 * right.carry5[ingress[1]]) % 7,
            ),
        )

    def repeat(
        self, count: int, *, ledger: ResourceLedger | None = None
    ) -> Q19CarryPhi6Summary:
        if type(count) is not int or count < 0:
            raise ValueError("Phi6 carry repetition count must be nonnegative")
        return binary_power(
            self,
            count,
            identity=Q19CarryPhi6Summary.identity(),
            compose=lambda first, second: first.then(second, ledger=ledger),
        ).value

    def phi6(self, at3: int, at5: int) -> tuple[int, int]:
        from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
            phi6_coefficients_from_root_values_mod7,
        )

        return phi6_coefficients_from_root_values_mod7(at3, at5)

    def carry_phi6(self, incoming: int = 0) -> tuple[int, int]:
        if type(incoming) is not int or incoming not in (0, 1):
            raise ValueError("incoming decimal carry must be zero or one")
        return self.phi6(self.carry3[incoming], self.carry5[incoming])

    def aligned_difference_mod7(self) -> int:
        """The existing D=99*(K//10)+10*g port, using true forward carry."""
        if not self.length:
            raise ValueError("aligned difference needs a nonempty pair word")
        growth = self.carry_exit(0)
        if self.length < 2:
            return 3 * growth % 7
        internal5 = (self.carry5[0] - growth * pow(5, (self.length - 1) % 6, 7)) % 7
        reversed_internal = internal5 * pow(3, (self.length - 2) % 6, 7) % 7
        return (reversed_internal + 3 * growth) % 7


@dataclass(frozen=True, slots=True)
class Q19CarryPhi6WordSummary:
    forward: Q19CarryPhi6Summary
    reverse: Q19CarryPhi6Summary
    prefix_forward: Q19CarryPhi6Summary
    prefix_reverse: Q19CarryPhi6Summary

    @classmethod
    def identity(cls) -> Q19CarryPhi6WordSummary:
        empty = Q19CarryPhi6Summary.identity()
        return cls(empty, empty, empty, empty)
