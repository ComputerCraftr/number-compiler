"""Chronological finite relation algebra for conditional carry transfers.

Rows encode successor sets as bitsets. Composition describes all paths through
the supplied relations; it supplies no certificate that a physical source can
follow an independently chosen sequence of boundary inputs.
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from typing import Generic, TypeVar

_State = TypeVar("_State", bound=Hashable)


@dataclass(frozen=True, slots=True, eq=False)
class BooleanStateSpace(Generic[_State]):
    """Identity-bearing owner for the states indexed by a Boolean matrix.

    The ordered state tuple defines row and column coordinates. Equality
    intentionally uses object identity: matching dimensions or labels do not
    authorize composition across independently issued spaces.
    """

    identity: str
    states: tuple[_State, ...]

    def __post_init__(self) -> None:
        if (
            type(self.identity) is not str
            or not self.identity
            or type(self.states) is not tuple
            or len(set(self.states)) != len(self.states)
        ):
            raise ValueError(
                "Boolean state space needs a name and unique ordered states"
            )

    @property
    def size(self) -> int:
        return len(self.states)


@dataclass(frozen=True, slots=True)
class BooleanMatrix(Generic[_State]):
    """Typed Boolean relation whose coordinates have one state-space owner."""

    state_space: BooleanStateSpace[_State]
    rows: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.state_space) is not BooleanStateSpace:
            raise TypeError("Boolean matrix requires an explicit state-space owner")
        if (
            type(self.rows) is not tuple
            or len(self.rows) != self.state_space.size
            or any(
                type(row) is not int or not 0 <= row < 1 << self.state_space.size
                for row in self.rows
            )
        ):
            raise ValueError("Boolean matrix rows do not match their state space")

    @classmethod
    def identity(cls, state_space: BooleanStateSpace[_State]) -> BooleanMatrix[_State]:
        if type(state_space) is not BooleanStateSpace:
            raise TypeError("Boolean identity requires an explicit state-space owner")
        return cls(
            state_space,
            tuple(1 << state for state in range(state_space.size)),
        )

    def then(self, later: BooleanMatrix[_State]) -> BooleanMatrix[_State]:
        if type(later) is not BooleanMatrix:
            raise TypeError("Boolean composition requires another typed matrix")
        if self.state_space is not later.state_space:
            raise ValueError("Boolean matrices have different state-space identities")
        return BooleanMatrix(self.state_space, boolean_rows_then(self.rows, later.rows))

    def power(self, count: int) -> BooleanMatrix[_State]:
        return BooleanMatrix(self.state_space, boolean_rows_power(self.rows, count))

    def image(self, source_bitset: int) -> int:
        return boolean_rows_image(self.rows, source_bitset)

    @property
    def edge_count(self) -> int:
        return sum(row.bit_count() for row in self.rows)


def _check_rows(rows: tuple[int, ...]) -> None:
    if type(rows) is not tuple:
        raise ValueError("Boolean transfer rows must be an immutable tuple")
    bound = 1 << len(rows)
    if any(type(row) is not int or not 0 <= row < bound for row in rows):
        raise ValueError("Boolean transfer rows must stay inside their state space")


def _image(rows: tuple[int, ...], sources: int) -> int:
    result = 0
    while sources:
        bit = sources & -sources
        result |= rows[bit.bit_length() - 1]
        sources ^= bit
    return result


def _then(first: tuple[int, ...], after: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(_image(after, row) for row in first)


def boolean_rows_then(
    first: tuple[int, ...], after: tuple[int, ...]
) -> tuple[int, ...]:
    """Apply ``first`` and then ``after``, retaining every allowed successor."""
    if len(first) != len(after):
        raise ValueError("Boolean transfer state spaces differ")
    _check_rows(first)
    _check_rows(after)
    return _then(first, after)


def boolean_rows_power(rows: tuple[int, ...], count: int) -> tuple[int, ...]:
    """Binary power of a supplied relation, including the identity at zero."""
    _check_rows(rows)
    if type(count) is not int or count < 0:
        raise ValueError("Boolean transfer power must be a nonnegative integer")
    result = tuple(1 << state for state in range(len(rows)))
    block = rows
    remaining = count
    while remaining:
        if remaining & 1:
            result = _then(result, block)
        remaining >>= 1
        if remaining:
            block = _then(block, block)
    return result


def boolean_rows_image(rows: tuple[int, ...], source_bitset: int) -> int:
    """Apply the relation to a set of states."""
    _check_rows(rows)
    if type(source_bitset) is not int or not 0 <= source_bitset < 1 << len(rows):
        raise ValueError("Boolean transfer sources must stay inside their state space")
    return _image(rows, source_bitset)


__all__ = [
    "BooleanMatrix",
    "BooleanStateSpace",
    "boolean_rows_image",
    "boolean_rows_power",
    "boolean_rows_then",
]
