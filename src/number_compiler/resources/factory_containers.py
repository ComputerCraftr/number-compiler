"""Factories and identity provenance for ledger-owned containers."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sized
from typing import TYPE_CHECKING, TypeVar

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger

ContainerKeyT = TypeVar("ContainerKeyT")
ContainerValueT = TypeVar("ContainerValueT")
ContainerItemT = TypeVar("ContainerItemT")


class FactoryContainerRegistry:
    """Track which retained stores were issued by the ledger's factories."""

    __slots__ = ("_identities",)

    def __init__(self) -> None:
        self._identities: set[int] = set()

    @property
    def audit_identity(self) -> int:
        """Keep the bookkeeping identity available to immutable audit records."""
        return id(self._identities)

    def discard(self, identity: int) -> None:
        self._identities.discard(identity)

    def contains(self, container: object) -> bool:
        return id(container) in self._identities

    def make_dict(
        self,
        ledger: ResourceLedger,
        owner: int,
        *,
        nodes_per_entry: int = 0,
        write_once: bool = False,
        key_type: type[ContainerKeyT] | None = None,
        value_type: type[ContainerValueT] | None = None,
    ) -> LedgerDict[ContainerKeyT, ContainerValueT]:
        """Create and atomically register a typed ledger-owned map."""
        if (key_type is None) != (value_type is None):
            raise TypeError("map type parameters must be supplied together")
        require_integer(nodes_per_entry, "nodes per entry", 0)
        if type(write_once) is not bool:
            raise TypeError("mapping write-once policy must be Boolean")
        result: LedgerDict[ContainerKeyT, ContainerValueT] = LedgerDict(
            ledger, owner, nodes_per_entry, write_once=write_once
        )
        self._register(
            ledger,
            owner,
            result,
            node_count=lambda: len(result) * nodes_per_entry,
            payloads=lambda: result.items(),
        )
        return result

    def make_list(
        self,
        ledger: ResourceLedger,
        owner: int,
        *,
        nodes_per_entry: int = 1,
        append_only: bool = True,
        item_type: type[ContainerItemT] | None = None,
    ) -> LedgerList[ContainerItemT]:
        """Create and atomically register a typed ledger-owned list."""
        require_integer(nodes_per_entry, "nodes per entry", 0)
        if type(append_only) is not bool:
            raise TypeError("append_only must be a boolean")
        result: LedgerList[ContainerItemT] = LedgerList(
            ledger, owner, nodes_per_entry, append_only
        )
        self._register(
            ledger,
            owner,
            result,
            node_count=lambda: len(result) * nodes_per_entry,
            payloads=lambda: result,
        )
        return result

    def _register(
        self,
        ledger: ResourceLedger,
        owner: int,
        container: Sized,
        *,
        node_count: Callable[[], int],
        payloads: Callable[[], Iterable[object]],
    ) -> None:
        identity = id(container)
        self._identities.add(identity)
        try:
            ledger.register_container(
                owner,
                container,
                node_count=node_count,
                payloads=payloads,
            )
        except BaseException:
            try:
                attached = ledger.account_status(owner).container_identity == identity
            except BaseException:
                attached = False
            if not attached:
                self._identities.discard(identity)
            raise


__all__ = [
    "ContainerItemT",
    "ContainerKeyT",
    "ContainerValueT",
    "FactoryContainerRegistry",
]
