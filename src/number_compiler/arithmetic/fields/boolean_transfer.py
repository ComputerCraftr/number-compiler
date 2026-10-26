"""Chronological finite relation algebra for conditional carry transfers.

Rows encode successor sets as bitsets. Composition describes all paths through
the supplied relations; it supplies no certificate that a physical source can
follow an independently chosen sequence of boundary inputs.
"""

from __future__ import annotations

from collections.abc import Hashable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
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


@dataclass(frozen=True, slots=True, eq=False)
class BooleanSparseRows(Generic[_State]):
    """Sparse indexed rows owned by one nominal Boolean state space.

    Each pair contains a source-state index and a nonzero successor bitset.
    Empty rows are omitted. The nominal state-space object prevents two
    same-sized but semantically different relations from being composed.
    """

    state_space: BooleanStateSpace[_State]
    rows: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        if type(self.state_space) is not BooleanStateSpace:
            raise TypeError("sparse Boolean rows need a state-space owner")
        if type(self.rows) is not tuple:
            raise TypeError("sparse Boolean rows must be an immutable tuple")
        previous = -1
        bound = 1 << self.state_space.size
        for row in self.rows:
            if type(row) is not tuple or len(row) != 2:
                raise TypeError("each sparse Boolean row must be an index pair")
            source, successors = row
            if (
                type(source) is not int
                or not 0 <= source < self.state_space.size
                or source <= previous
                or type(successors) is not int
                or not 0 < successors < bound
            ):
                raise ValueError("sparse Boolean rows are malformed or unsorted")
            previous = source

    @classmethod
    def from_mapping(
        cls,
        state_space: BooleanStateSpace[_State],
        rows: Mapping[int, int],
    ) -> BooleanSparseRows[_State]:
        """Validate indexed rows and canonicalize them in source order."""
        if type(state_space) is not BooleanStateSpace:
            raise TypeError("sparse Boolean rows need a state-space owner")
        bound = 1 << state_space.size
        canonical: list[tuple[int, int]] = []
        for source, successors in rows.items():
            if (
                type(source) is not int
                or not 0 <= source < state_space.size
                or type(successors) is not int
                or not 0 <= successors < bound
            ):
                raise ValueError("sparse Boolean row lies outside its state space")
            if successors:
                canonical.append((source, successors))
        return BooleanSparseRows[_State](state_space, tuple(sorted(canonical)))

    def as_mapping(self) -> Mapping[int, int]:
        """Expose read-only canonical rows for consumers and metrics owners."""
        return MappingProxyType(dict(self.rows))

    @property
    def edge_count(self) -> int:
        return sum(successors.bit_count() for _, successors in self.rows)


@dataclass(frozen=True, slots=True)
class BooleanSparseComposition(Generic[_State]):
    """Sparse chronological product with work measured at actual row visits."""

    rows: BooleanSparseRows[_State]
    intermediate_edges_visited: int
    row_joins: int
    joined_target_edges: int
    result_edges: int

    def __post_init__(self) -> None:
        if type(self.rows) is not BooleanSparseRows:
            raise TypeError("sparse Boolean composition needs result rows")
        if type(self.intermediate_edges_visited) is not int or (
            self.intermediate_edges_visited < 0
        ):
            raise ValueError("invalid sparse composition edge-visit count")
        if type(self.row_joins) is not int or (
            self.row_joins != self.intermediate_edges_visited
        ):
            raise ValueError("sparse composition join count is inconsistent")
        if type(self.joined_target_edges) is not int or (self.joined_target_edges < 0):
            raise ValueError("invalid sparse composition edge count")
        if (
            type(self.result_edges) is not int
            or self.result_edges != self.rows.edge_count
        ):
            raise ValueError("sparse composition result edge count is inconsistent")


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


def boolean_sparse_rows_then(
    first: BooleanSparseRows[_State], later: BooleanSparseRows[_State]
) -> BooleanSparseComposition[_State]:
    """Chronologically compose sparse rows, retaining all reachable targets.

    The first two counters count actual intermediate-edge visits and row
    joins. ``joined_target_edges`` is a logical relation-cardinality measure
    (the total population of the selected later rows), not an operation count:
    the implementation unions their bitsets without enumerating each edge. A
    middle state with no later row is a valid dead end and contributes zero
    joined targets. These counters do not represent source or period authority.
    """
    if type(first) is not BooleanSparseRows or type(later) is not BooleanSparseRows:
        raise TypeError("sparse Boolean composition requires typed row owners")
    if first.state_space is not later.state_space:
        raise ValueError("sparse Boolean relations have different state spaces")
    later_rows = dict(later.rows)
    composed: dict[int, int] = {}
    intermediate_visits = 0
    row_joins = 0
    joined_targets = 0
    for source, middle_bitset in first.rows:
        result = 0
        remaining = middle_bitset
        while remaining:
            middle_bit = remaining & -remaining
            middle = middle_bit.bit_length() - 1
            intermediate_visits += 1
            row_joins += 1
            successors = later_rows.get(middle, 0)
            joined_targets += successors.bit_count()
            result |= successors
            remaining ^= middle_bit
        if result:
            composed[source] = result
    result_rows = BooleanSparseRows[_State].from_mapping(first.state_space, composed)
    return BooleanSparseComposition(
        result_rows,
        intermediate_visits,
        row_joins,
        joined_targets,
        result_rows.edge_count,
    )


__all__ = [
    "BooleanSparseComposition",
    "BooleanSparseRows",
    "BooleanMatrix",
    "BooleanStateSpace",
    "boolean_sparse_rows_then",
    "boolean_rows_image",
    "boolean_rows_power",
    "boolean_rows_then",
]
