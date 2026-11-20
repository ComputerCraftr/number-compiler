"""Identity-checked finite weighted relation algebra.

Each edge carries a fixed tuple of additive integer weights. State-space and
law objects are nominal authorities: equal sizes or labels do not authorize a
join between independently defined coordinates or weight meanings.
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from typing import Generic, TypeVar

from number_compiler.arithmetic.fields.boolean_transfer import BooleanStateSpace

_State = TypeVar("_State", bound=Hashable)
WeightedEntry = tuple[int, ...]
WeightedRows = tuple[tuple[WeightedEntry, ...], ...]


@dataclass(frozen=True, slots=True)
class WeightedRowPowerResult:
    """Exact pointed result and separate work for a transfer power."""

    row: tuple[WeightedEntry, ...]
    row_evaluations: int
    matrix_compositions: int
    matrix_squarings: int
    used_branching_fallback: bool

    def __post_init__(self) -> None:
        if type(self.row) is not tuple or any(
            type(entry) is not tuple
            or not entry
            or any(type(value) is not int for value in entry)
            for entry in self.row
        ):
            raise ValueError("pointed weighted result has a malformed row")
        if any(
            type(work) is not int or work < 0
            for work in (
                self.row_evaluations,
                self.matrix_compositions,
                self.matrix_squarings,
            )
        ):
            raise ValueError("pointed weighted result has invalid work counters")
        if type(self.used_branching_fallback) is not bool:
            raise TypeError("pointed weighted fallback marker must be Boolean")


def _compose_entry(first: WeightedEntry, later: WeightedEntry) -> WeightedEntry:
    return (
        later[0],
        *(left + right for left, right in zip(first[1:], later[1:], strict=True)),
    )


@dataclass(frozen=True, slots=True, eq=False)
class WeightedTransferLaw:
    """Identity-bearing declaration of an ordered additive-weight tuple."""

    name: str
    weight_names: tuple[str, ...]

    def __post_init__(self) -> None:
        if (
            type(self.name) is not str
            or not self.name
            or type(self.weight_names) is not tuple
            or not self.weight_names
            or any(type(name) is not str or not name for name in self.weight_names)
            or len(set(self.weight_names)) != len(self.weight_names)
        ):
            raise ValueError("weighted transfer law needs named additive coordinates")


@dataclass(frozen=True, slots=True)
class WeightedTransfer(Generic[_State]):
    """Finite weighted relation owned by one nominal state space and law."""

    state_space: BooleanStateSpace[_State]
    law: WeightedTransferLaw
    rows: WeightedRows

    def __post_init__(self) -> None:
        if type(self.state_space) is not BooleanStateSpace:
            raise TypeError("weighted transfer needs an explicit state-space owner")
        if type(self.law) is not WeightedTransferLaw:
            raise TypeError("weighted transfer needs an explicit law owner")
        if type(self.rows) is not tuple or len(self.rows) != self.state_space.size:
            raise ValueError("weighted transfer rows differ from their state space")
        expected_entry_size = len(self.law.weight_names) + 1
        for row in self.rows:
            if type(row) is not tuple or any(
                type(entry) is not tuple
                or len(entry) != expected_entry_size
                or any(type(value) is not int for value in entry)
                or not 0 <= entry[0] < self.state_space.size
                for entry in row
            ):
                raise ValueError("weighted transfer contains an invalid edge")

    @classmethod
    def identity(
        cls,
        state_space: BooleanStateSpace[_State],
        law: WeightedTransferLaw,
    ) -> WeightedTransfer[_State]:
        if type(state_space) is not BooleanStateSpace:
            raise TypeError("weighted identity needs a state-space owner")
        if type(law) is not WeightedTransferLaw:
            raise TypeError("weighted identity needs a law owner")
        return cls(
            state_space,
            law,
            tuple(
                ((index,) + (0,) * len(law.weight_names),)
                for index in range(state_space.size)
            ),
        )

    def then(
        self,
        later: WeightedTransfer[_State],
        *,
        max_row_entries: int = 512,
    ) -> WeightedTransfer[_State]:
        """Compose chronologically, retaining every distinct weighted path."""
        if type(later) is not WeightedTransfer:
            raise TypeError("weighted composition requires another typed transfer")
        if self.state_space is not later.state_space:
            raise ValueError("weighted transfers have different state-space identities")
        if self.law is not later.law:
            raise ValueError("weighted transfers have different law identities")
        if type(max_row_entries) is not int or not 1 <= max_row_entries <= 10000:
            raise ValueError("weighted transfer composition has invalid row budget")

        if all(len(row) <= 1 for row in self.rows) and all(
            len(row) <= 1 for row in later.rows
        ):
            result: list[tuple[WeightedEntry, ...]] = []
            for row in self.rows:
                if not row:
                    result.append(())
                    continue
                source_entry = row[0]
                successor_row = later.rows[source_entry[0]]
                if not successor_row:
                    result.append(())
                    continue
                result.append((_compose_entry(source_entry, successor_row[0]),))
            return WeightedTransfer(self.state_space, self.law, tuple(result))

        result = []
        for row in self.rows:
            paths: set[WeightedEntry] = set()
            for source_entry in row:
                for successor_entry in later.rows[source_entry[0]]:
                    paths.add(_compose_entry(source_entry, successor_entry))
                    if len(paths) > max_row_entries:
                        raise ValueError("weighted transfer row exceeds its budget")
            result.append(tuple(sorted(paths)))
        return WeightedTransfer(self.state_space, self.law, tuple(result))

    def power(
        self,
        exponent: int,
        *,
        max_row_entries: int = 512,
    ) -> WeightedTransfer[_State]:
        result, _, _ = self.power_with_work(exponent, max_row_entries=max_row_entries)
        return result

    def power_with_work(
        self,
        exponent: int,
        *,
        max_row_entries: int = 512,
    ) -> tuple[WeightedTransfer[_State], int, int]:
        if type(exponent) is not int or exponent < 0:
            raise ValueError("weighted transfer power needs a natural exponent")
        result: WeightedTransfer[_State] = self.identity(self.state_space, self.law)
        base = self
        compositions = 0
        squarings = 0
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = result.then(base, max_row_entries=max_row_entries)
                compositions += 1
            remaining >>= 1
            if remaining:
                base = base.then(base, max_row_entries=max_row_entries)
                compositions += 1
                squarings += 1
        return result, compositions, squarings

    def power_row_with_work(
        self,
        source: int,
        exponent: int,
        *,
        max_row_entries: int = 512,
    ) -> WeightedRowPowerResult:
        """Power one row, cycling deterministic paths and exactly falling back.

        If every encountered row is deterministic, a repeated state gives an
        exact weighted cycle whose additive payload can be multiplied without
        constructing the full powered matrix. If any encountered row branches,
        the general matrix power is used and retains every weighted outcome.
        The row probe work and matrix-product work are reported separately.
        """
        if type(source) is not int or not 0 <= source < self.state_space.size:
            raise ValueError("pointed weighted source lies outside its state space")
        if type(exponent) is not int or exponent < 0:
            raise ValueError("pointed weighted power needs a natural exponent")
        if type(max_row_entries) is not int or not 1 <= max_row_entries <= 10000:
            raise ValueError("pointed weighted power has an invalid row budget")
        if exponent == 0:
            return WeightedRowPowerResult(
                ((source,) + (0,) * len(self.law.weight_names),),
                0,
                0,
                0,
                False,
            )

        seen: dict[int, tuple[int, tuple[int, ...]]] = {}
        accumulated = [0] * len(self.law.weight_names)
        state = source
        elapsed = 0
        row_evaluations = 0
        while elapsed < exponent:
            previous = seen.get(state)
            if previous is not None:
                cycle_start, start_weights = previous
                cycle_length = elapsed - cycle_start
                if cycle_length <= 0:
                    raise ArithmeticError("weighted deterministic cycle is empty")
                repeats = (exponent - elapsed) // cycle_length
                if repeats:
                    for index, start_weight in enumerate(start_weights):
                        accumulated[index] += (
                            accumulated[index] - start_weight
                        ) * repeats
                    elapsed += cycle_length * repeats
                    if elapsed == exponent:
                        break
                # At most one unskipped suffix shorter than a cycle remains.
                seen.clear()
                continue
            seen[state] = (elapsed, tuple(accumulated))
            row = self.rows[state]
            row_evaluations += 1
            if len(row) > 1:
                powered, compositions, squarings = self.power_with_work(
                    exponent, max_row_entries=max_row_entries
                )
                return WeightedRowPowerResult(
                    powered.rows[source],
                    row_evaluations,
                    compositions,
                    squarings,
                    True,
                )
            if not row:
                return WeightedRowPowerResult((), row_evaluations, 0, 0, False)
            edge = row[0]
            state = edge[0]
            for index, weight in enumerate(edge[1:]):
                accumulated[index] += weight
            elapsed += 1

        return WeightedRowPowerResult(
            ((state, *accumulated),), row_evaluations, 0, 0, False
        )


__all__ = [
    "WeightedEntry",
    "WeightedRows",
    "WeightedRowPowerResult",
    "WeightedTransfer",
    "WeightedTransferLaw",
]
