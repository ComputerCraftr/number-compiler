"""Owned retained mappings and authenticated temporary ledger reservations."""

from __future__ import annotations

from collections.abc import (
    Callable,
    Generator,
    Iterable,
    Iterator,
    Mapping,
    MutableMapping,
)
from contextlib import contextmanager
from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, NamedTuple, Self, TypeVar, cast
from weakref import ReferenceType, ref

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


class _OwnedMemoConsumerClaim:
    """One transaction-wide claim shared by a consumer's related memos."""

    __slots__ = ("_committed", "_binding_identity", "_consumer_reference")

    def __setattr__(self, name: str, value: object) -> None:
        if name not in (
            "_committed",
            "_binding_identity",
            "_consumer_reference",
        ) or hasattr(self, name):
            raise AttributeError("memo consumer claim state is immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("memo consumer claim state is immutable")

    def __init__(self, consumer: object) -> None:
        self._committed = False
        self._binding_identity = object()
        self._consumer_reference: ReferenceType[object] = ref(consumer)

    @property
    def committed(self) -> bool:
        return self._committed

    @property
    def binding_identity(self) -> object:
        return self._binding_identity

    @property
    def consumer_reference(self) -> ReferenceType[object]:
        return self._consumer_reference

    def commit(self) -> None:
        if self._committed:
            raise ValueError("memo consumer claim is already committed")
        object.__setattr__(self, "_committed", True)


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
    consumer_claimed: bool
    consumer_claim_committed: bool
    consumer_claim_identity: object | None
    consumer_reference: ReferenceType[object] | None
    container: Mapping[_K, _V | DynamicMemoValue[_V]]

    @property
    def consumer(self) -> object | None:
        """Resolve the exact memo consumer without extending its lifetime."""
        return None if self.consumer_reference is None else self.consumer_reference()

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
        self._consumer_claim: _OwnedMemoConsumerClaim | None = None
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
            self._consumer_claim is not None,
            (
                self._consumer_claim.committed
                if self._consumer_claim is not None
                else False
            ),
            (
                self._consumer_claim.binding_identity
                if self._consumer_claim is not None
                else None
            ),
            (
                self._consumer_claim.consumer_reference
                if self._consumer_claim is not None
                else None
            ),
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

    def _owned_store(self) -> LedgerDict[_K, _V | DynamicMemoValue[_V]]:
        """Validate the retained mapping at publication and rollback boundaries."""
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
        return data

    def _rollback_failed_store_publication(
        self,
        key: _K,
        stored_value: _V | DynamicMemoValue[_V],
    ) -> bool:
        """Remove only the exact row written by a failed insertion."""
        data = self._owned_store()
        marker = object()
        current = data.get(key, marker)
        if current is marker:
            return False
        if current is not stored_value:
            raise RuntimeError("failed memo publication found a different value")
        if not data.rollback_inserted_value(key, stored_value):
            raise RuntimeError("failed memo publication row disappeared")
        return True

    def _release_failed_publication_charge(self, *, entries: int, nodes: int) -> None:
        """Release a failed row charge or retain its exact retry delta."""
        pending_entries = self._pending_clear_entries + entries
        pending_nodes = self._pending_clear_nodes + nodes
        self._record_pending_clear(pending_entries, pending_nodes)
        clear_accounted_store(
            self.ledger,
            self.owner,
            lambda: None,
            self._measure_store,
            (pending_entries, pending_nodes),
            self._record_pending_clear,
        )

    def _measure_store(self) -> tuple[int, int]:
        size = len(self._data)
        if self.node_cost is None:
            return size, size * self.nodes_per_entry
        nodes = 0
        for value in self._data.values():
            if not isinstance(value, DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            nodes += value.nodes
        return size, nodes

    def _record_pending_clear(self, entries: int, nodes: int) -> None:
        self._pending_clear_entries, self._pending_clear_nodes = entries, nodes

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
        stored_value: _V | DynamicMemoValue[_V] = value
        try:
            if self.node_cost is not None:
                stored_value = DynamicMemoValue(value, nodes)
            self._data[key] = stored_value
        except BaseException as error:
            cleanup_error: BaseException | None = None
            try:
                self._rollback_failed_store_publication(key, stored_value)
                self._release_failed_publication_charge(entries=1, nodes=nodes)
            except BaseException as failure:
                cleanup_error = failure
            stored_value = cast(_V | DynamicMemoValue[_V], None)
            value = cast(_V, None)
            if cleanup_error is not None:
                raise error from cleanup_error
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
        data = self._owned_store()
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
        data = self._owned_store()

        nodes = self.entry_nodes(key, value)
        previous_dynamic_nodes = self._dynamic_nodes
        next_dynamic_nodes = previous_dynamic_nodes + nodes
        # Allocate the wrapper before transferring ownership; even an
        # allocation-time BaseException then leaves the source scope intact.
        stored = DynamicMemoValue(value, nodes)
        owner_before = self.ledger.account_usage(self.owner)
        try:
            reservation.transfer_to(self.owner, entries=1, nodes=nodes)
            data[key] = cast(_V | DynamicMemoValue[_V], stored)
            self._dynamic_nodes = next_dynamic_nodes
        except BaseException as error:
            cleanup_error: BaseException | None = None
            try:
                self._rollback_failed_store_publication(key, stored)
                self._dynamic_nodes = previous_dynamic_nodes
                owner_after = self.ledger.account_usage(self.owner)
                owner_delta = (
                    owner_after[0] - owner_before[0],
                    owner_after[1] - owner_before[1],
                )
                if owner_delta == (1, nodes):
                    try:
                        reservation.transfer_from(self.owner, entries=1, nodes=nodes)
                    except BaseException as transfer_error:
                        after_transfer = self.ledger.account_usage(self.owner)
                        remaining_delta = (
                            after_transfer[0] - owner_before[0],
                            after_transfer[1] - owner_before[1],
                        )
                        if remaining_delta == (1, nodes):
                            try:
                                self._release_failed_publication_charge(
                                    entries=1, nodes=nodes
                                )
                            except BaseException as release_error:
                                raise transfer_error from release_error
                        elif remaining_delta != (0, 0):
                            raise RuntimeError(
                                "memo adoption rollback changed unrelated accounting"
                            ) from transfer_error
                        raise
                elif owner_delta != (0, 0):
                    raise RuntimeError(
                        "memo adoption failure changed unrelated accounting"
                    )
            except BaseException as rollback_error:
                cleanup_error = rollback_error
            stored = cast(DynamicMemoValue[_V], None)
            value = cast(_V, None)
            if cleanup_error is not None:
                raise error from cleanup_error
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

        def clear_store() -> None:
            try:
                self._data.clear()
            finally:
                if self.node_cost is not None:
                    self._dynamic_nodes = self._measure_store()[1]

        clear_accounted_store(
            self.ledger,
            self.owner,
            clear_store,
            self._measure_store,
            (self._pending_clear_entries, self._pending_clear_nodes),
            self._record_pending_clear,
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

    @staticmethod
    @contextmanager
    def claim_empty_consumer(
        memos: tuple[OwnedMemo[object, object], ...],
        *,
        ledger: ResourceLedger,
        consumer: object,
    ) -> Generator[object, None, None]:
        """Atomically bind one consumer to empty memos on one ledger.

        The claim is shared across all stores and becomes immutable only after
        the caller's binding block completes. Clearing or disposing a memo
        never releases a committed consumer claim.
        """
        from number_compiler.resources.ledger import ResourceLedger
        from number_compiler.resources.stores import LedgerDict

        if type(ledger) is not ResourceLedger:
            raise TypeError("memo consumer claim requires its exact resource ledger")
        if type(memos) is not tuple or not memos:
            raise ValueError("memo consumer claim requires a nonempty exact tuple")
        if any(type(memo) is not OwnedMemo for memo in memos):
            raise TypeError("memo consumer claim requires exact owned memos")
        if any(
            first is second
            for index, first in enumerate(memos)
            for second in memos[index + 1 :]
        ):
            raise ValueError("memo consumer claim requires distinct stores")
        if len({memo.owner for memo in memos}) != len(memos):
            raise ValueError("memo consumer claim requires distinct resource owners")
        snapshots = tuple(memo.audit_snapshot() for memo in memos)
        containers = tuple(snapshot.container for snapshot in snapshots)
        if any(
            first is second
            for index, first in enumerate(containers)
            for second in containers[index + 1 :]
        ):
            raise ValueError("memo consumer claim requires distinct backing stores")
        for memo, snapshot in zip(memos, snapshots, strict=True):
            memo._check_open()
            account = ledger.account_status(memo.owner)
            raw_container: object = snapshot.container
            if type(raw_container) is not LedgerDict:
                raise ValueError("memo consumer owner audit failed")
            container = cast(LedgerDict[object, object], raw_container)
            if (
                memo.ledger is not ledger
                or snapshot.ledger is not ledger
                or snapshot.owner != memo.owner
                or snapshot.disposed
                or snapshot.consumer_claimed
                or snapshot.consumer_claim_committed
                or snapshot.consumer_claim_identity is not None
                or len(memo) != 0
                or memo.audit_container is not container
                or container.ledger is not ledger
                or container.owner != memo.owner
                or account.disposed
                or ledger.registered_container(memo.owner) is not container
                or not ledger.is_factory_container(container)
            ):
                raise ValueError("memo consumer owner audit failed")

        # Constructing the weak reference may fail for a non-weak-referenceable
        # consumer. Do this before the first memo receives the provisional claim.
        claim = _OwnedMemoConsumerClaim(consumer)
        try:
            for memo in memos:
                memo._consumer_claim = claim
            yield claim.binding_identity
            claim.commit()
        except BaseException as error:
            try:
                if claim.committed:
                    raise ValueError(
                        "committed memo consumer claim cannot be rolled back"
                    )
                for memo in reversed(memos):
                    if memo._consumer_claim is claim:
                        object.__setattr__(memo, "_consumer_claim", None)
            except BaseException as cleanup_error:
                raise cleanup_error from error
            raise
