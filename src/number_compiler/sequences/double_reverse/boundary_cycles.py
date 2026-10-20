"""Exact two-cell edge transition graph for T(x)=2*rev10(x).

This module deliberately distinguishes a *candidate cyclic SCC* of the
boundary overapproximation from a source-certified temporal macro. The only
unconditional two-cell recurrent cylinder is the previous 1144/2288 macro;
three further cyclic components have interior-carry-dependent exit ports.
Shrinking paths require a deeper trailing-digit halo and are NEVER dropped.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, TypeGuard

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)

Edge: TypeAlias = tuple[int, int, int, int]  # first 2, last 2, MSDF


def is_edge_tuple(value: object) -> TypeGuard[Edge]:
    """Accept only an exact four-int decimal boundary tuple."""
    return (
        is_exact_object_tuple(value)
        and len(value) == 4
        and all(type(digit) is int and 0 <= digit <= 9 for digit in value)
    )


@dataclass(frozen=True, slots=True)
class BoundaryStep:
    target: Edge
    width_delta: int  # +1 growth, 0 preserved
    inward_carry: int | None  # None iff the branch is carry-independent


@dataclass(frozen=True, slots=True)
class BoundaryRelation:
    """Candidate edges or an explicit shrinking frontier needing more halo."""

    steps: tuple[BoundaryStep, ...]
    shrinking_frontier: bool

    def __post_init__(self) -> None:
        if type(self.shrinking_frontier) is not bool:
            raise TypeError("boundary frontier tag must be Boolean")
        if self.shrinking_frontier == bool(self.steps):
            raise ValueError("boundary relation must be either edges or shrink")


# Canonical SCCs of the complete nonshrinking edge graph. The first is
# forward-closed for every inward carry; the other three have explicit exits.
_C0 = frozenset(
    {
        (1, 7, 4, 2),
        (1, 7, 6, 8),
        (1, 7, 8, 8),
        (4, 8, 4, 2),
        (4, 8, 6, 8),
        (4, 8, 8, 8),
        (4, 9, 4, 2),
        (4, 9, 6, 8),
        (4, 9, 8, 8),
    }
)
_C1 = frozenset(
    {
        (1, 6, 6, 8),
        (1, 6, 8, 8),
        (1, 7, 2, 2),
        (4, 5, 4, 2),
        (4, 8, 0, 8),
        (4, 9, 0, 8),
    }
)
_C2 = frozenset(
    {
        (1, 6, 4, 2),
        (1, 7, 0, 8),
        (4, 5, 6, 8),
        (4, 5, 8, 8),
        (4, 8, 2, 2),
        (4, 9, 2, 2),
    }
)
_C3 = frozenset(
    {
        (1, 6, 0, 8),
        (1, 6, 2, 2),
        (4, 5, 0, 8),
        (4, 5, 2, 2),
    }
)
CANDIDATE_COMPONENTS = (_C0, _C1, _C2, _C3)


def edge_from_digits(digits: str) -> Edge:
    """Return canonical two-cell boundary (requires width >= 5)."""
    if (
        len(digits) < 5
        or digits[0] not in "123456789"
        or not (digits.isascii() and digits.isdigit())
    ):
        raise ValueError("two-cell boundary requires a >=5-digit positive numeral")
    return (int(digits[0]), int(digits[1]), int(digits[-2]), int(digits[-1]))


def candidate_component(edge: Edge) -> int | None:
    """A candidate *SCC*, not permission to temporally power the source."""
    for index, states in enumerate(CANDIDATE_COMPONENTS):
        if edge in states:
            return index
    return None


def boundary_steps(edge: Edge) -> BoundaryRelation:
    """Return complete candidate edges or explicitly mark a shrink frontier.

    The carry from the third-last source digit is either 0 or 1. In the
    shrinking case the new leading TWO digits depend on additional inward
    digits, so this function returns a typed deeper-halo frontier, not an
    empty edge set that could be mistaken for a dead trajectory. Exact
    contraction length is determined separately by width_change().
    """
    a, b, y, z = edge
    if not (1 <= a <= 9 and 0 <= b <= 9 and 0 <= y <= 9 and 0 <= z <= 9):
        raise ValueError("noncanonical two-cell source")
    lower = ((2 * b + int(a >= 5)) % 10, (2 * a) % 10)
    if z >= 5:
        return BoundaryRelation(
            (BoundaryStep((1, (2 * z + int(y >= 5)) % 10, *lower), 1, None),),
            False,
        )
    top = 2 * z + int(y >= 5)
    if top == 0:
        return BoundaryRelation((), True)
    return BoundaryRelation(
        tuple(
            BoundaryStep((top, (2 * y + carry) % 10, *lower), 0, carry)
            for carry in (0, 1)
        ),
        False,
    )


def width_change(source: str) -> int:
    """Exact change of physical width for EVERY positive decimal source.

    If X=A*10**k with 10 not dividing A, then
        width(T(X))-width(X) == -k + [A%10>=5].
    After any positive first step k is either 0 or 1. For X=0 width remains 1.
    """
    if (
        not source
        or not (source.isascii() and source.isdigit())
        or (source[0] == "0" and source != "0")
    ):
        raise ValueError("source must be canonical nonnegative decimal")
    if source == "0":
        return 0
    zeros = len(source) - len(source.rstrip("0"))
    return -zeros + int(int(source[-1 - zeros]) >= 5)
