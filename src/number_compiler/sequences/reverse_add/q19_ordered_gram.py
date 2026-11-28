"""Ordered two-inlet carry correlations for Q19 pair-sum words.

Each row records one pair of incoming carries.  The five signed polynomial
channels use the source word's least-significant-first coordinate.  Their
coefficients are evaluated at z + epsilon in a truncated polynomial ring.
Source admission and memory ownership belong to the issuing caller.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.polynomials.primary_jet import (
    primary_jet_add,
    primary_jet_multiply,
    primary_jet_scale,
)

Jet = tuple[int, ...]


@dataclass(frozen=True, slots=True)
class Q19GramRow:
    """The response for one ordered pair of incoming carry bits."""

    left_exit: int
    right_exit: int
    a: Jet
    b: Jet
    ab: Jet
    a_next_b: Jet
    next_a_b: Jet
    first_a: int
    last_a: int
    first_b: int
    last_b: int


@dataclass(frozen=True, slots=True)
class Q19OrderedGramAction:
    """Four conditional rows and their position shifts in one coefficient ring."""

    z: int
    modulus: int
    degree: int
    length: int
    power: Jet
    before_last: Jet
    rows: tuple[Q19GramRow, ...]

    @classmethod
    def identity(cls, z: int, modulus: int, degree: int) -> Q19OrderedGramAction:
        if (
            type(z) is not int
            or type(modulus) is not int
            or modulus < 2
            or type(degree) is not int
            or not 1 <= degree <= 9
        ):
            raise ValueError(
                "Gram action requires an integer ring and 1–9 coefficients"
            )
        zero = (0,) * degree
        one = (1,) + (0,) * (degree - 1)
        rows = tuple(
            Q19GramRow(a, b, zero, zero, zero, zero, zero, 0, 0, 0, 0)
            for a in (0, 1)
            for b in (0, 1)
        )
        return cls(z % modulus, modulus, degree, 0, one, one, rows)

    @classmethod
    def atom(
        cls, symbol: int, z: int, modulus: int, degree: int
    ) -> Q19OrderedGramAction:
        if type(symbol) is not int or not 0 <= symbol <= 18:
            raise ValueError("Q19 pair sum must be in 0..18")
        identity = cls.identity(z, modulus, degree)
        zero = (0,) * degree
        tail = (0,) * (degree - 1)
        rows = tuple(
            Q19GramRow(
                (symbol + a) // 10,
                (symbol + b) // 10,
                ((1 - 2 * a) % modulus,) + tail,
                ((1 - 2 * b) % modulus,) + tail,
                (((1 - 2 * a) * (1 - 2 * b)) % modulus,) + tail,
                zero,
                zero,
                (1 - 2 * a) % modulus,
                (1 - 2 * a) % modulus,
                (1 - 2 * b) % modulus,
                (1 - 2 * b) % modulus,
            )
            for a in (0, 1)
            for b in (0, 1)
        )
        power = (identity.z,) + ((1,) if degree > 1 else ()) + (0,) * max(0, degree - 2)
        return cls(identity.z, modulus, degree, 1, power, identity.power, rows)

    def then(
        self,
        upper: Q19OrderedGramAction,
        *,
        on_compose: Callable[[], None] | None = None,
    ) -> Q19OrderedGramAction:
        """Append an ordered word, preserving its two correlated inlet carries."""
        if type(upper) is not Q19OrderedGramAction or (
            self.z,
            self.modulus,
            self.degree,
        ) != (upper.z, upper.modulus, upper.degree):
            raise ValueError("Gram actions require the same coefficient ring")
        if not self.length:
            return upper
        if not upper.length:
            return self
        if on_compose is not None:
            on_compose()
        modulus = self.modulus

        def append(left: Jet, right: Jet) -> Jet:
            return primary_jet_add(
                left, primary_jet_multiply(self.power, right, modulus), modulus
            )

        def join(left_carry: int, right_carry: int) -> Q19GramRow:
            left_exit = self.rows[2 * left_carry].left_exit
            right_exit = upper.rows[right_carry].right_exit
            left = self.rows[2 * left_carry + right_exit]
            right = upper.rows[2 * left_exit + right_carry]
            first_cross = primary_jet_add(
                append(left.a_next_b, right.a_next_b),
                primary_jet_scale(
                    self.before_last, left.last_a * right.first_b, modulus
                ),
                modulus,
            )
            second_cross = primary_jet_add(
                append(left.next_a_b, right.next_a_b),
                primary_jet_scale(
                    self.before_last, left.last_b * right.first_a, modulus
                ),
                modulus,
            )
            return Q19GramRow(
                right.left_exit,
                left.right_exit,
                append(left.a, right.a),
                append(left.b, right.b),
                append(left.ab, right.ab),
                first_cross,
                second_cross,
                left.first_a,
                right.last_a,
                left.first_b,
                right.last_b,
            )

        rows = tuple(join(a, b) for a in (0, 1) for b in (0, 1))
        return Q19OrderedGramAction(
            self.z,
            modulus,
            self.degree,
            self.length + upper.length,
            primary_jet_multiply(self.power, upper.power, modulus),
            primary_jet_multiply(self.power, upper.before_last, modulus),
            rows,
        )

    def repeat(
        self, count: int, *, on_compose: Callable[[], None] | None = None
    ) -> Q19OrderedGramAction:
        """Power an ordered word without expanding its represented copies."""
        if type(count) is not int or count < 0:
            raise ValueError("Gram repetition count must be a nonnegative integer")
        return binary_power(
            self,
            count,
            identity=self.identity(self.z, self.modulus, self.degree),
            compose=lambda left, right: left.then(right, on_compose=on_compose),
        ).value
