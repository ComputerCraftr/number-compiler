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


__all__ = [
    "WeightedEntry",
    "WeightedRows",
    "WeightedTransfer",
    "WeightedTransferLaw",
]
