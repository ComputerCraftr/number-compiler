"""Simultaneous port substitution with a transactionally published reduced DAG.

Only Boolean functions are staged. Cofactor states contain original decision
IDs and replacement decision IDs, never sampled values of a spatial field.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import (
    PortComponent,
    PortVariable,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_port_action import (
        FinitePortActionArena,
    )


@dataclass(frozen=True, slots=True)
class SubstitutionKey:
    function: TransferSummaryID
    components: tuple[PortComponent, ...]

    def __post_init__(self) -> None:
        if (
            type(self.function) is not TransferSummaryID
            or self.function.kind != "finite-port-function"
        ):
            raise ValueError("invalid substitution function")
        if type(self.components) is not tuple or any(
            type(part) is not PortComponent for part in self.components
        ):
            raise ValueError("invalid substitution components")
        variables = tuple(part.variable for part in self.components)
        if variables != tuple(sorted(set(variables))):
            raise ValueError("substitution components must be ordered and unique")
        for part in self.components:
            part.function.validate(self.function.owner, "finite-port-function")


@dataclass(frozen=True, slots=True)
class PortIndexComponent:
    variable: PortVariable
    function: int


@dataclass(frozen=True, slots=True)
class SubstitutionIndexKey:
    function: int
    components: tuple[PortIndexComponent, ...]


# -1 is an implicit identity variable, not a Boolean decision ID.


class FinitePortSubstitution:
    def __init__(self, arena: FinitePortActionArena) -> None:
        self.arena = arena
        self.ledger = arena.ledger
        prefix = f"finite-port-substitution-{len(self.ledger.inventory())}"
        self.memo_owner = self.ledger.register(prefix, "query_memo")
        self.support_owner = self.ledger.register(prefix + "-support", "query_memo")
        self.memo: MutableMapping[SubstitutionIndexKey, int] = self.ledger.make_dict(
            self.memo_owner
        )
        self.supports: MutableMapping[int, tuple[PortVariable, ...]] = (
            self.ledger.make_dict(self.support_owner)
        )
        self.ledger.register_container(
            self.memo_owner,
            self.memo,
            node_count=lambda: 0,
            payloads=lambda: self.memo.items(),
            evict=self.clear,
            composition_count=lambda: len(self.memo),
        )
        self.ledger.register_container(
            self.support_owner,
            self.supports,
            node_count=lambda: 0,
            payloads=lambda: self.supports.items(),
        )

    def clear(self) -> None:
        entries, supports = len(self.memo), len(self.supports)
        self.memo.clear()
        self.supports.clear()
        self.ledger.release(self.memo_owner, entries=entries)
        self.ledger.release(self.support_owner, entries=supports)

    def record_peak(self, name: str, size: int) -> None:
        self.ledger.bump(name, max(0, size - self.ledger.counters.get(name, 0)))

    def apply(
        self,
        function: TransferSummaryID,
        substitutions: Mapping[PortVariable, TransferSummaryID],
    ) -> TransferSummaryID:
        return self.arena.compile_substitution(self, function, substitutions)
