"""Owned retained mappings and authenticated temporary ledger reservations."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator, Mapping, MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, NamedTuple, Self, TypeVar, cast

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.lifecycle import clear_accounted_store
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger

_K = TypeVar("_K")
_V = TypeVar("_V")


class OwnedMemoAuditPayloadView(Mapping[_K, object], Generic[_K]):
    """Zero-copy, read-only view of memo payloads for forensic audits.

    Dynamic cost wrappers are checked when read. This view is deliberately
    independent of memo liveness and counters, so completed audits can inspect
    a disposed memo's still-retained backing container.
    """

    __slots__ = ("_container", "_dynamic_cost")

    def __init__(
        self,
        container: Mapping[_K, object],
        *,
        dynamic_cost: bool,
    ) -> None:
        self._container = container
        self._dynamic_cost = dynamic_cost

    def __getitem__(self, key: _K) -> object:
        stored = self._container[key]
        if not self._dynamic_cost:
            return stored
        if type(stored) is not DynamicMemoValue:
            raise TypeError("dynamic memo entry has invalid cost metadata")
        dynamic = cast(DynamicMemoValue[object], stored)
        if type(dynamic.nodes) is not int or dynamic.nodes < 1:
            raise TypeError("dynamic memo entry has invalid cost metadata")
        return dynamic.value

    def __iter__(self) -> Iterator[_K]:
        return iter(self._container)

    def __len__(self) -> int:
        return len(self._container)

    @property
    def backing_store_identity(self) -> object:
        """Expose identity only, without handing out a mutable backing API."""
        return self._container


class LedgerReservation:
    """Track real temporary ledger charges that may be adopted atomically.

    A transfer is checked against the source owner's live ledger account and
    against charges acquired through this tracker. It therefore cannot mint
    unbacked node credit or adopt another workspace's unrelated reservation.
    """

    __slots__ = ("_ledger",)

    def __setattr__(self, name: str, value: object) -> None:
        if name != "_ledger" or hasattr(self, "_ledger"):
            raise AttributeError("ledger reservation binding is immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("ledger reservation binding is immutable")

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        from number_compiler.resources.ledger import ResourceLedger

        if type(ledger) is not ResourceLedger:
            raise TypeError("reservation needs its exact ResourceLedger")
        self._ledger = ledger
        ledger.register_reservation(self, owner)

    def _check_open(self) -> None:
        self._ledger.validate_reservation(self)

    def belongs_to(self, ledger: ResourceLedger) -> bool:
        """Check ledger identity without exposing the reservation binding."""
        return self._ledger is ledger

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Return the exact ledger bound to this reservation."""
        return self._ledger

    def reserve(self, *, entries: int = 0, nodes: int = 0) -> None:
        self._check_open()
        self._ledger.reserve_for_reservation(self, entries=entries, nodes=nodes)

    def transfer_to(self, owner: int, *, entries: int = 0, nodes: int = 0) -> None:
        self._check_open()
        self._ledger.transfer_reservation_to(self, owner, entries=entries, nodes=nodes)

    def release(self, *, entries: int = 0, nodes: int = 0) -> None:
        """Return temporary capacity without touching another scope's charges."""
        self._check_open()
        self._ledger.release_for_reservation(self, entries=entries, nodes=nodes)

    def transfer_from(self, owner: int, *, entries: int = 0, nodes: int = 0) -> None:
        self._check_open()
        self._ledger.transfer_reservation_from(
            self, owner, entries=entries, nodes=nodes
        )

    def close(self) -> None:
        self._ledger.close_reservation(self)

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()


class DynamicMemoValue(NamedTuple, Generic[_V]):
    """Payload and its retained cost stored together in the owned mapping."""

    value: _V
    nodes: int


@dataclass(frozen=True, slots=True)
class OwnedMemoAuditSnapshot(Generic[_K, _V]):
    """Read-only state needed to verify an owned memo's resource binding."""

    ledger: ResourceLedger
    owner: int
    nodes_per_entry: int
    dynamic_cost: bool
    dynamic_nodes: int
    pending_clear_entries: int
    pending_clear_nodes: int
    disposed: bool
    container: Mapping[_K, _V | DynamicMemoValue[_V]]

    @property
    def payload_view(self) -> OwnedMemoAuditPayloadView[_K]:
        """View payload values while preserving the exact raw container identity."""
        return OwnedMemoAuditPayloadView(
            self.container,
            dynamic_cost=self.dynamic_cost,
        )


class OwnedMemo(MutableMapping[_K, _V], Generic[_K, _V]):
    """An inventoried memo with fixed or payload-dependent node reservations."""

    def __init__(
        self,
        ledger: ResourceLedger,
        owner: int,
        *,
        nodes_per_entry: int = 0,
        node_cost: Callable[[_K, _V], int] | None = None,
        evictable: bool = False,
        composition_entries: bool = False,
    ) -> None:
        require_integer(nodes_per_entry, "nodes per entry", 0)
        if type(evictable) is not bool or type(composition_entries) is not bool:
            raise TypeError("memo policy flags must be booleans")
        if node_cost is not None and nodes_per_entry:
            raise ValueError("dynamic memo cost cannot be combined with a fixed cost")
        self.ledger = ledger
        self.owner = owner
        self.nodes_per_entry = nodes_per_entry
        self.node_cost = node_cost
        self._dynamic_nodes = 0
        self._pending_clear_entries = self._pending_clear_nodes = 0
        self._disposed = False
        self._data: MutableMapping[_K, _V | DynamicMemoValue[_V]] = ledger.make_dict(
            owner, nodes_per_entry=nodes_per_entry
        )
        ledger.register_execution_root(self)
        ledger.register_container(
            owner,
            self._data,
            node_count=self._node_count,
            payloads=self._payloads,
            evict=self._evict if evictable else None,
            composition_count=self._entry_count if composition_entries else None,
        )

    def _check_open(self) -> None:
        if self._disposed:
            raise RuntimeError("memo has been disposed")

    @property
    def audit_container(
        self,
    ) -> Mapping[_K, _V | DynamicMemoValue[_V]]:
        """Expose the exact registered store through a read-only audit view."""
        self._check_open()
        return self._data

    def audit_snapshot(self) -> OwnedMemoAuditSnapshot[_K, _V]:
        """Return immutable accounting metadata and the exact registered map."""
        return OwnedMemoAuditSnapshot(
            self.ledger,
            self.owner,
            self.nodes_per_entry,
            self.node_cost is not None,
            self._dynamic_nodes,
            self._pending_clear_entries,
            self._pending_clear_nodes,
            self._disposed,
            self._data,
        )

    def audit_payload_view(self) -> OwnedMemoAuditPayloadView[_K]:
        """Read retained payloads without requiring an open memo or charging work."""
        return self.audit_snapshot().payload_view

    def _entry_count(self) -> int:
        return len(self._data)

    def _node_count(self) -> int:
        if self.node_cost is not None:
            return self._dynamic_nodes
        return len(self._data) * self.nodes_per_entry

    def entry_nodes(self, key: _K, value: _V) -> int:
        if self.node_cost is None:
            return self.nodes_per_entry
        payload_nodes = require_integer(
            self.node_cost(key, value), "memo payload node cost", 0
        )
        # One retained node accounts for the immutable cost metadata wrapper.
        return payload_nodes + 1

    def _payloads(self) -> Iterable[object]:
        from number_compiler.resources.payload_containers import audit_mapping_items

        for key, value in audit_mapping_items(self):
            yield key
            yield value

    def _audited_value(self, value: object) -> object:
        if self.node_cost is None:
            return value
        if not isinstance(value, DynamicMemoValue):
            raise TypeError("dynamic memo entry has invalid cost metadata")
        dynamic = cast(DynamicMemoValue[object], value)
        return dynamic.value

    def __getitem__(self, key: _K) -> _V:
        self._check_open()
        value = self._data[key]
        if self.node_cost is not None:
            if not isinstance(value, DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            dynamic = cast(DynamicMemoValue[_V], value)
            return dynamic.value
        return cast(_V, value)

    def __setitem__(self, key: _K, value: _V) -> None:
        self._check_open()
        if key in self._data:
            if self.node_cost is None:
                self._data[key] = value
                return
            previous = self._data[key]
            if not isinstance(previous, DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            old_cost = previous.nodes
            new_cost = self.entry_nodes(key, value)
            difference = new_cost - old_cost
            if difference > 0:
                self.ledger.reserve(self.owner, nodes=difference)
            try:
                self._data[key] = DynamicMemoValue(value, new_cost)
            except BaseException:
                self._data[key] = previous
                if difference > 0:
                    self.ledger.release(self.owner, nodes=difference)
                raise
            self._dynamic_nodes += difference
            if difference < 0:
                self.ledger.release(self.owner, nodes=-difference)
            return
        nodes = self.entry_nodes(key, value)
        self.ledger.reserve(self.owner, entries=1, nodes=nodes)
        try:
            if self.node_cost is not None:
                stored_value: _V | DynamicMemoValue[_V] = DynamicMemoValue(value, nodes)
            else:
                stored_value = value
            self._data[key] = stored_value
        except BaseException:
            if key in self._data:
                del self._data[key]
            self.ledger.release(self.owner, entries=1, nodes=nodes)
            raise
        if self.node_cost is not None:
            self._dynamic_nodes += nodes

    def publish_reserved(self, key: _K, value: _V) -> None:
        """Publish a fixed-cost entry charged by an earlier ledger reservation.

        The retained mapping rechecks the reservation at its write boundary.
        This method deliberately adds no charge; its caller owns rollback of a
        reservation if publication fails.
        """
        self._check_open()
        if self.node_cost is not None:
            raise TypeError("reserved direct publication requires fixed memo cost")
        raw_data: object = self._data
        if type(raw_data) is not LedgerDict:
            raise RuntimeError("memo lost its ledger-owned mapping")
        data = cast(LedgerDict[_K, _V | DynamicMemoValue[_V]], raw_data)
        if (
            data.ledger is not self.ledger
            or data.owner != self.owner
            or not self.ledger.is_factory_container(data)
        ):
            raise RuntimeError("memo lost its ledger-owned mapping")
        if key in data:
            raise KeyError("reserved memo publication requires a new key")
        data[key] = value

    def adopt_reserved(
        self,
        key: _K,
        value: _V,
        reservation: LedgerReservation,
    ) -> None:
        """Publish a dynamic entry by transferring its exact cost from a scope.

        Failed insertion returns the charge to the source tracker, whose normal
        context cleanup then releases the workspace exactly once.
        """
        self._check_open()
        if self.node_cost is None:
            raise TypeError("reservation adoption requires a dynamic-cost memo")
        if type(reservation) is not LedgerReservation:
            raise TypeError("memo adoption needs an exact ledger reservation")
        if not reservation.belongs_to(self.ledger):
            raise ValueError("memo and reservation belong to different ledgers")
        if key in self._data:
            raise KeyError("reserved memo publication requires a new key")
        raw_data: object = self._data
        if type(raw_data) is not LedgerDict:
            raise RuntimeError("dynamic memo lost its ledger-owned mapping")
        data = cast(LedgerDict[_K, _V | DynamicMemoValue[_V]], raw_data)
        if (
            data.ledger is not self.ledger
            or data.owner != self.owner
            or not self.ledger.is_factory_container(data)
        ):
            raise RuntimeError("dynamic memo lost its ledger-owned mapping")

        nodes = self.entry_nodes(key, value)
        previous_dynamic_nodes = self._dynamic_nodes
        next_dynamic_nodes = previous_dynamic_nodes + nodes
        # Allocate the wrapper before transferring ownership; even an
        # allocation-time BaseException then leaves the source scope intact.
        stored = DynamicMemoValue(value, nodes)
        reservation.transfer_to(self.owner, entries=1, nodes=nodes)
        try:
            data[key] = cast(_V | DynamicMemoValue[_V], stored)
            self._dynamic_nodes = next_dynamic_nodes
        except BaseException as error:
            try:
                marker = object()
                current = data.get(key, marker)
                if current is stored:
                    del data[key]
                elif current is not marker:
                    raise RuntimeError(
                        "failed memo publication found a different value"
                    )
                self._dynamic_nodes = previous_dynamic_nodes
                try:
                    reservation.transfer_from(self.owner, entries=1, nodes=nodes)
                except BaseException:
                    # If the charge cannot be returned to the workspace, drop
                    # it from the target account so failed publication leaves
                    # neither retained data nor an orphan reservation.
                    self.ledger.release(self.owner, entries=1, nodes=nodes)
                    raise
            except BaseException as rollback_error:
                raise rollback_error from error
            raise

    def __delitem__(self, key: _K) -> None:
        self._check_open()
        value = self._data[key]
        if self.node_cost is not None:
            if not isinstance(value, DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            nodes = value.nodes
        else:
            nodes = self.nodes_per_entry
        del self._data[key]
        if self.node_cost is not None:
            self._dynamic_nodes -= nodes
        self.ledger.release(self.owner, entries=1, nodes=nodes)

    def __len__(self) -> int:
        self._check_open()
        return len(self._data)

    def __iter__(self) -> Iterator[_K]:
        self._check_open()
        return iter(self._data)

    def clear(self) -> None:
        self._check_open()

        def measure() -> tuple[int, int]:
            size = len(self._data)
            if self.node_cost is None:
                return size, size * self.nodes_per_entry
            nodes = 0
            for value in self._data.values():
                if not isinstance(value, DynamicMemoValue):
                    raise TypeError("dynamic memo entry has invalid cost metadata")
                nodes += value.nodes
            return size, nodes

        def clear_store() -> None:
            try:
                self._data.clear()
            finally:
                if self.node_cost is not None:
                    self._dynamic_nodes = measure()[1]

        def record_pending(entries: int, nodes: int) -> None:
            self._pending_clear_entries, self._pending_clear_nodes = entries, nodes

        clear_accounted_store(
            self.ledger,
            self.owner,
            clear_store,
            measure,
            (self._pending_clear_entries, self._pending_clear_nodes),
            record_pending,
        )

    def _evict(self) -> None:
        if not self._disposed:
            self.clear()

    def dispose(self) -> None:
        """Release actual memo values and invalidate every future lookup/update.

        A ledger owns its registered containers for its lifetime. Disposing a
        memo empties that container; dropping the owning index/ledger releases
        remaining canonical arenas through ordinary garbage collection.
        """
        if self._disposed:
            return
        self.clear()
        self.ledger.mark_disposed(self.owner)
        self._disposed = True
