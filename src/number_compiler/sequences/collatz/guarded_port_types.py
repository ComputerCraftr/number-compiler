"""Typed requests and guarded rows shared by the Collatz port join."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.cross_family_port_power import (
    SourceCongruence,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_radix6_bridge import FiveBand


@dataclass(frozen=True, slots=True)
class PortPuncture:
    """Request only observed ports; absent values are not inferred."""

    input_pair: int | None = None
    upper_parity: int | None = None
    output_pair: int | None = None
    tens: int | None = None
    hundreds: int | None = None
    five_carry: int | None = None
    five_remainder: int | None = None
    future_border: int | None = None
    upper_word: tuple[int, int, int] | None = None
    numerator_f5: int | None = None

    def __post_init__(self) -> None:
        for key, maximum in (
            ("input_pair", 99),
            ("upper_parity", 1),
            ("output_pair", 99),
            ("tens", 2),
            ("hundreds", 2),
            ("five_carry", 2),
            ("five_remainder", 1),
            ("future_border", 9),
            ("numerator_f5", 4),
        ):
            value = getattr(self, key)
            if value is not None and (
                type(value) is not int or not 0 <= value <= maximum
            ):
                raise ValueError(f"invalid Collatz puncture {key}")
        if self.upper_word is not None:
            if (
                type(self.upper_word) is not tuple
                or len(self.upper_word) != 3
                or any(type(value) is not int for value in self.upper_word)
            ):
                raise ValueError("upper-word puncture needs (width, digits, word)")
            width, digits, word = self.upper_word
            if (
                not 1 <= digits <= width <= 1024
                or not 6 ** (digits - 1) <= word < 6**digits
            ):
                raise ValueError("upper-word puncture has impossible base-6 digits")


@dataclass(frozen=True, slots=True)
class GuardedCarryRow:
    """One guarded nonzero of the weighted decimal pair relation."""

    root_guard: SourceCongruence
    root: CollatzTwoSidedCylinder
    time: int
    input_pair: int
    upper_parity: int
    odd: int
    output_pair: int
    tens: int
    hundreds: int
    target: CollatzTwoSidedCylinder
    forced_fives: tuple[FiveBand, ...]

    @property
    def count(self) -> int:
        return self.root.count


@dataclass(frozen=True, slots=True)
class GuardedPortCut:
    """A source-partitioned, source-authorized time slice of the relation."""

    time: int
    root: CollatzTwoSidedCylinder
    rows: tuple[GuardedCarryRow, ...]
    forced_fives: tuple[FiveBand, ...]
    prefix: DyadicTerminalFieldAction
    prefix_scalar_steps: int = 0

    @property
    def admitted_count(self) -> int:
        return sum(row.count for row in self.rows)

    def pointed(self, source: int) -> GuardedCarryRow | None:
        if not self.root.contains(source):
            raise ValueError("pointed source outside cut source class")
        matched = tuple(row for row in self.rows if row.root.contains(source))
        if len(matched) > 1:
            raise ArithmeticError("guarded pair relation has overlapping source rows")
        return matched[0] if matched else None


__all__ = ["GuardedCarryRow", "GuardedPortCut", "PortPuncture"]
