"""Research-only emitting carry actions for alternating 2,3 weights over F5.

Rows are extensional boundary-port functions, not temporal successor states.
The 501 bound is length-indexed: all-EQ emissions depend on length modulo ten.
No pointwise carry/value field is recoverable from these two harmonic sums.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

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
