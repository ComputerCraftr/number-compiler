"""Research-only emitting carry actions for alternating 2,3 weights over F5.

Rows are extensional boundary-port functions, not temporal successor states.
The 501 bound is length-indexed: all-EQ emissions depend on length modulo ten.
No pointwise carry/value field is recoverable from these two harmonic sums.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)

Harmonics = tuple[int, int]
PortRow = tuple[int, int, int]
PortRows = tuple[PortRow, PortRow]


def harmonic_sum(values: Iterable[int]) -> Harmonics:
    """Reference observation; construction/composition does not call this."""
    even = odd = 0
    for index, value in enumerate(values):
        if index % 2:
            odd += value
        else:
            even += value
    return population_harmonics(even, odd)


def population_harmonics(even: int, odd: int) -> Harmonics:
    return (even + 2 * odd) % 5, (even + 3 * odd) % 5


def populations(h0: int, h1: int) -> Harmonics:
    return (3 * h0 - 2 * h1) % 5, (h1 - h0) % 5


def prefix_harmonics(length: int) -> Harmonics:
    if type(length) is not int or length < 0:
        raise ValueError("prefix length must be an exact nonnegative integer")
    return population_harmonics((length + 1) // 2, length // 2)


def compose_rows(left: PortRows, right: PortRows, left_parity: int) -> PortRows:
    """Port substitution and alternating phase transport for either emission."""
    require_endpoint_construction()
    if type(left_parity) is not int or left_parity not in (0, 1):
        raise ValueError("spatial phase must be a bit")
    rows: list[PortRow] = []
    for midpoint, h0, h1 in left:
        outgoing, r0, r1 = right[midpoint]
        if left_parity:
            r0, r1 = 2 * r1, 3 * r0
        rows.append((outgoing, (h0 + r0) % 5, (h1 + r1) % 5))
    return rows[0], rows[1]


@dataclass(frozen=True, slots=True)
class CarryHarmonicPortAction:
    """Exact spatial width plus two carry-occupancy emission rows."""

    width: int
    rows: PortRows

    def __post_init__(self) -> None:
        require_endpoint_construction()
        if type(self.width) is not int or self.width < 0:
            raise ValueError("carry harmonic width must be nonnegative and exact")
        if type(self.rows) is not tuple or len(self.rows) != 2:
            raise ValueError("two immutable carry-port rows required")
        for row in self.rows:
            if (
                type(row) is not tuple
                or len(row) != 3
                or any(type(v) is not int for v in row)
                or row[0] not in (0, 1)
                or any(not 0 <= v < 5 for v in row[1:])
            ):
                raise ValueError("invalid carry/harmonic output row")

    @classmethod
    def empty(cls) -> CarryHarmonicPortAction:
        return cls(0, ((0, 0, 0), (1, 0, 0)))

    @classmethod
    def leaf(cls, domain: CarryFn) -> CarryHarmonicPortAction:
        return cls(
            1,
            ((apply_carry_fn(domain, 0), 0, 0), (apply_carry_fn(domain, 1), 1, 1)),
        )

    def then(self, right: CarryHarmonicPortAction) -> CarryHarmonicPortAction:
        return CarryHarmonicPortAction(
            self.width + right.width,
            compose_rows(self.rows, right.rows, self.width % 2),
        )

    @classmethod
    def from_domains(cls, domains: Iterable[CarryFn]) -> CarryHarmonicPortAction:
        result = cls.empty()
        for domain in domains:
            result = result.then(cls.leaf(domain))
        return result

    def border_rows(self) -> PortRows:
        """Project C[i+1]-C[i] using width phase and the same occupancy action."""
        result: list[PortRow] = []
        for incoming, (outgoing, h0, h1) in enumerate(self.rows):
            even, odd = populations(h0, h1)
            f0, f1 = population_harmonics(
                odd - even + outgoing * (self.width % 2),
                even - odd - incoming + outgoing * (1 - self.width % 2),
            )
            result.append((outgoing, f0, f1))
        return result[0], result[1]

    def punctured_border(self) -> PuncturedCarryHarmonic:
        """Project the active border; the all-Equal row remains the puncture.

        This spatial projection forgets occupancy and source occurrence. It
        grants no temporal successor authority.
        """
        return PuncturedCarryHarmonic.from_border_rows(self.border_rows())

    def length_indexed_code(self) -> tuple[int, ...]:
        """501 possibilities at fixed length, NOT an untyped semantic key."""
        zero, one = self.rows
        if zero[0] != one[0]:
            if self.rows != ((0, 0, 0), (1, *prefix_harmonics(self.width))):
                raise ValueError("not a realizable identity carry action")
            return (0,)
        difference = ((one[1] - zero[1]) % 5, (one[2] - zero[2]) % 5)
        for prefix in range(10):
            if prefix_harmonics(prefix) == difference:
                return (1, zero[0], prefix, zero[1], zero[2])
        raise ValueError("not a realizable decisive-prefix emission")

    def forcing_harmonics(self) -> Harmonics:
        """Whole symmetric decimal field, physical incoming carry zero only."""
        if not self.width:
            raise ValueError("empty geometry has no reverse/add forcing")
        growth, h0, h1 = self.rows[0]
        even, odd = populations(h0, h1)
        if growth:
            even += 1  # Replace C0=0 by the new edge 1 before reflection.
        output_width = self.width + growth
        reflected_even, reflected_odd = (even, odd) if output_width % 2 else (odd, even)
        return population_harmonics(even + reflected_even, odd + reflected_odd)


@dataclass(frozen=True, slots=True)
class PuncturedCarryHarmonic:
    """One exact nonidentity border projection, with width kept externally.

    ``then_even`` and ``power_even`` require an even-width occurrence. Decoding
    rows does not authenticate that phase or any temporal source cylinder.
    Zero centered harmonics are active idempotents, not the identity puncture.
    """

    outgoing: int
    decisive_parity: int
    harmonic: int

    def __post_init__(self) -> None:
        require_endpoint_construction()
        if type(self.outgoing) is not int or self.outgoing not in (0, 1):
            raise ValueError("punctured outgoing carry must be a bit")
        if type(self.decisive_parity) is not int or self.decisive_parity not in (0, 1):
            raise ValueError("punctured decisive parity must be a bit")
        if type(self.harmonic) is not int or not 0 <= self.harmonic < 5:
            raise ValueError("punctured harmonic coordinate must lie in F5")

    @property
    def dependent_harmonic(self) -> int:
        """Second F5 border coordinate, forced by the punctured code."""
        return (2 * self.harmonic - self.outgoing) % 5

    @property
    def centered(self) -> int:
        """F5 diagonal coordinate whose even-width square is multiplication by 2."""
        return (self.harmonic - self.outgoing * (1 + self.decisive_parity)) % 5

    @property
    def idempotent_center(self) -> int:
        return (self.outgoing * (1 + self.decisive_parity)) % 5

    def then_even(self, right: "PuncturedCarryHarmonic") -> "PuncturedCarryHarmonic":
        """Compose two nonidentity blocks when the left width is even.

        The first decisive domain remains in the left block, while the outgoing
        carry is the right block's outgoing carry.  No carry-domain word is
        reconstructed.
        """
        if type(right) is not PuncturedCarryHarmonic:
            raise TypeError("punctured harmonic composition needs another port")
        return PuncturedCarryHarmonic(
            right.outgoing,
            self.decisive_parity,
            (
                self.harmonic
                + right.harmonic
                - self.outgoing * (1 + right.decisive_parity)
            )
            % 5,
        )

    def square_even(self) -> "PuncturedCarryHarmonic":
        return self.then_even(self)

    def power_even(self, exponent: int) -> "PuncturedCarryHarmonic":
        """Repeat one even-width punctured block without replaying its domains."""
        if type(exponent) is not int or exponent < 1:
            raise ValueError("punctured harmonic exponent must be positive")
        # Closed form of repeated composition.  The Boolean sheet is fixed;
        # centered u scales by the exponent in F5.
        center = self.idempotent_center
        harmonic = (center + (exponent % 5) * self.centered) % 5
        return PuncturedCarryHarmonic(self.outgoing, self.decisive_parity, harmonic)

    def vieta_with(self, reflected: "PuncturedCarryHarmonic") -> tuple[int, int]:
        """Anonymous forward/reflection root pair over F5.

        Reflection-sheet metadata remains occurrence data outside this pair.
        The returned elementary symmetric coordinates are invariant under
        swapping the two roots.
        """
        if type(reflected) is not PuncturedCarryHarmonic:
            raise TypeError("Vieta pairing needs another punctured port")
        left, right = self.centered, reflected.centered
        return (left + right) % 5, (left * right) % 5

    @classmethod
    def from_border_rows(
        cls,
        rows: tuple[tuple[int, int, int], tuple[int, int, int]],
    ) -> "PuncturedCarryHarmonic":
        """Decode the exact 20-class nonidentity border parameterization.

        The sole identity/no-decision row is deliberately rejected: it is the
        puncture, not another active port.
        """
        if rows == ((0, 0, 0), (1, 0, 0)):
            raise ValueError("all-Equal/no-decision carry row is the punctured port")
        if type(rows) is not tuple or len(rows) != 2:
            raise ValueError("two immutable border rows are required")
        first, second = rows
        if any(type(row) is not tuple or len(row) != 3 for row in rows):
            raise ValueError("invalid border rows")
        if any(type(value) is not int for row in rows for value in row):
            raise ValueError("border coordinates require exact integers")
        outgoing, f0, f1 = first
        if (
            type(outgoing) is not int
            or outgoing not in (0, 1)
            or not all(type(v) is int and 0 <= v < 5 for v in (f0, f1))
        ):
            raise ValueError("invalid punctured border row")
        if f1 != (2 * f0 - outgoing) % 5:
            raise ValueError("border row violates the F5 harmonic relation")
        parity = None
        for candidate, (w0, w1) in enumerate(((1, 1), (2, 3))):
            if second == (
                outgoing,
                (f0 - w0) % 5,
                (f1 - w1) % 5,
            ):
                parity = candidate
                break
        if parity is None:
            raise ValueError("border row is not a punctured decisive-prefix action")
        return cls(outgoing, parity, f0)

    def border_rows(self) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
        f0 = self.harmonic
        f1 = self.dependent_harmonic
        w0, w1 = ((1, 1), (2, 3))[self.decisive_parity]
        return (
            (self.outgoing, f0, f1),
            (self.outgoing, (f0 - w0) % 5, (f1 - w1) % 5),
        )
