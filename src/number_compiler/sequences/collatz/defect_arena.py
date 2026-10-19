"""Frozen finite monoid for residual behavior left after Collatz factoring."""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger

_DEFECT_KIND = "collatz-residual-defect"


@dataclass(frozen=True, slots=True)
class CollatzDefectClassID(ArenaHandle):
    """A scoped class in one frozen residual-behavior certificate."""


class CollatzDefectArena:
    """An authenticated, exact finite monoid table for residual behavior."""

    def __init__(
        self,
        table: tuple[tuple[int, ...], ...],
        *,
        identity: int,
        ledger: ResourceLedger | None = None,
    ) -> None:
        if (
            type(table) is not tuple
            or not table
            or any(type(row) is not tuple for row in table)
        ):
            raise TypeError(
                "residual composition table must be a nonempty immutable matrix"
            )
        size = len(table)
        if type(identity) is not int:
            raise TypeError("residual identity must be an exact class index")
        if not 0 <= identity < size:
            raise ValueError("residual identity must be an exact class index")
        if any(len(row) != size for row in table):
            raise ValueError("residual composition table must be square")
        for row in table:
            for result in row:
                if type(result) is not int or not 0 <= result < size:
                    raise ValueError("residual composition table is not closed")
        for index in range(size):
            if table[identity][index] != index or table[index][identity] != index:
                raise ValueError("declared residual identity is invalid")
        for first in range(size):
            for second in range(size):
                for third in range(size):
                    if (
                        table[table[first][second]][third]
                        != table[first][table[second][third]]
                    ):
                        raise ValueError(
                            "residual composition table is not associative"
                        )
        self.owner = ArenaToken("collatz-residual-defects")
        self.ledger = ledger if ledger is not None else ResourceLedger()
        self.table = table
        self.identity_index = identity
        encoded = repr((size, identity, table)).encode("ascii")
        self.certificate_digest = sha256(encoded).hexdigest()

    @property
    def class_count(self) -> int:
        return len(self.table)

    @property
    def identity(self) -> CollatzDefectClassID:
        return self.class_id(self.identity_index)

    def class_id(self, index: int) -> CollatzDefectClassID:
        if type(index) is not int or not 0 <= index < self.class_count:
            raise ValueError("invalid residual class index")
        return CollatzDefectClassID(self.owner, _DEFECT_KIND, index)

    def validate(self, reference: CollatzDefectClassID) -> int:
        if type(reference) is not CollatzDefectClassID:
            raise TypeError("expected a scoped Collatz residual class")
        return reference.validate(
            self.owner,
            _DEFECT_KIND,
            size=self.class_count,
        ).local_id

    def compose(
        self,
        before: CollatzDefectClassID,
        after: CollatzDefectClassID,
    ) -> CollatzDefectClassID:
        before_id, after_id = self.validate(before), self.validate(after)
        return self.class_id(self.table[before_id][after_id])


__all__ = ("CollatzDefectArena", "CollatzDefectClassID")
