"""Ledger-created stores; builtin descriptors cannot bypass their boundaries.

Only these infrastructure wrappers own bare backing containers. Factories
register the wrapper before publication, and every insertion checks its prior
reservation. Canonical sequences are append-only for their whole lifetime.
"""

from __future__ import annotations

from collections.abc import (
    ItemsView,
    Iterable,
    Iterator,
    KeysView,
    Mapping,
    MutableMapping,
    MutableSequence,
    ValuesView,
)
from operator import index as as_index
from sys import getsizeof
from typing import (
    TYPE_CHECKING,
    Generic,
    Never,
    Protocol,
    Self,
    SupportsIndex,
    TypeVar,
    cast,
    overload,
)

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


K = TypeVar("K")
V = TypeVar("V")
V_co = TypeVar("V_co", covariant=True)
T = TypeVar("T")
NodeT = TypeVar("NodeT")
NodeKeyT = TypeVar("NodeKeyT")
UpdateK = TypeVar("UpdateK")
UpdateV = TypeVar("UpdateV")
UpdateV_contra = TypeVar("UpdateV_contra", contravariant=True)


class _SupportsKeysAndGetItem(Protocol[K, V_co]):
    """Mapping-like input accepted by the standard mapping update contract."""

    def keys(self) -> Iterable[K]: ...

    def __getitem__(self, key: K, /) -> V_co: ...


class _MappingUpdateTarget(Protocol[UpdateK, UpdateV_contra]):
    """Typed mutation seam shared by the two tracked-map owners."""

    def apply_update(self, values: Mapping[UpdateK, UpdateV_contra]) -> None: ...


class TrackedDict(dict[K, V]):
    """Backing map that invalidates audits even through adversarial test access."""

    def __init__(self, ledger: ResourceLedger) -> None:
        super().__init__()
        self._ledger = ledger

    def belongs_to(self, ledger: ResourceLedger) -> bool:
        """Check ledger identity without exposing the mutation hook owner."""
        return self._ledger is ledger

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Return the exact ledger that owns this tracked store."""
        return self._ledger

    def __setitem__(self, key: K, value: V) -> None:
        existed = key in self
        previous: dict[K, V] = {}
        if existed:
            previous[key] = dict[K, V].__getitem__(self, key)
        super().__setitem__(key, value)
        try:
            self._ledger.note_store_mutation()
        except BaseException:
            if existed:
                dict[K, V].__setitem__(self, key, previous[key])
            else:
                dict[K, V].__delitem__(self, key)
            try:
                self._ledger.note_store_mutation()
            except BaseException:
                pass
            raise

    def __delitem__(self, key: K) -> None:
        previous = dict[K, V].__getitem__(self, key)
        super().__delitem__(key)
        try:
            self._ledger.note_store_mutation()
        except BaseException:
            dict[K, V].__setitem__(self, key, previous)
            try:
                self._ledger.note_store_mutation()
            except BaseException:
                pass
            raise

    def clear(self) -> None:
        if self:
            previous = dict[K, V].copy(self)
            super().clear()
            try:
                self._ledger.note_store_mutation()
            except BaseException:
                dict[K, V].update(self, previous)
                try:
                    self._ledger.note_store_mutation()
                except BaseException:
                    pass
                raise

    def setdefault(self, key: K, default: V | None = None) -> V:
        if key in self:
            return self[key]
        result = super().setdefault(key, cast(V, default))
        try:
            self._ledger.note_store_mutation()
        except BaseException:
            dict[K, V].__delitem__(self, key)
            try:
                self._ledger.note_store_mutation()
            except BaseException:
                pass
            raise
        return result

    @overload
    def update(self, other: _SupportsKeysAndGetItem[K, V], /) -> None: ...

    @overload
    def update(
        self,
        other: Iterable[tuple[K, V]],
        /,
    ) -> None: ...

    @overload
    def update(
        self: TrackedDict[str, V],
        other: _SupportsKeysAndGetItem[str, V],
        /,
        **kwargs: V,
    ) -> None: ...

    @overload
    def update(
        self: TrackedDict[str, V],
        other: Iterable[tuple[str, V]],
        /,
        **kwargs: V,
    ) -> None: ...

    @overload
    def update(self: TrackedDict[str, V], /, **kwargs: V) -> None: ...

    def update(
        self: _MappingUpdateTarget[UpdateK, UpdateV],
        other: _SupportsKeysAndGetItem[UpdateK, UpdateV]
        | Iterable[tuple[UpdateK, UpdateV]] = (),
        /,
        **kwargs: UpdateV,
    ) -> None:
        self.apply_update(dict[UpdateK, UpdateV](other, **kwargs))

    def apply_update(self, values: Mapping[K, V]) -> None:
        if values:
            previous: dict[K, V] = {}
            new_keys: set[K] = set()
            for key in values:
                if key in self:
                    previous[key] = dict[K, V].__getitem__(self, key)
                else:
                    new_keys.add(key)
            super().update(values)
            try:
                self._ledger.note_store_mutation()
            except BaseException:
                for key in values:
                    if key in new_keys:
                        dict[K, V].__delitem__(self, key)
                    else:
                        dict[K, V].__setitem__(self, key, previous[key])
                try:
                    self._ledger.note_store_mutation()
                except BaseException:
                    pass
                raise


class _TrackedList(list[T]):
    """Backing sequence with the same mutation contract as retained maps."""

    def __init__(self, ledger: ResourceLedger) -> None:
        super().__init__()
        self._ledger = ledger
        self._mutation_identity = object()
        self._mutation_version = 0

    def _changed(self) -> None:
        self._mutation_version += 1
        self._ledger.note_store_mutation()

    @property
    def mutation_stamp(self) -> tuple[object, int]:
        """Expose mutation authority without leaking its protected fields."""
        return self._mutation_identity, self._mutation_version

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Return the exact ledger that owns this tracked store."""
        return self._ledger

    def __iter__(self) -> Iterator[T]:
        return list[T].__iter__(self)

    def append(self, value: T) -> None:
        original_length = len(self)
        appended = False
        try:
            super().append(value)
            appended = True
            self._changed()
        except BaseException:
            if (
                appended
                and len(self) > original_length
                and self[original_length] is value
            ):
                # _changed may fail after the list itself has accepted the
                # value. Roll back only this exact append slot; a concurrent
                # or otherwise legitimate suffix must not be discarded.
                list[T].__delitem__(self, original_length)
                self._mutation_version += 1
                try:
                    self._ledger.note_store_mutation()
                except BaseException:
                    # Keep the publication error authoritative. The mutation
                    # stamp still changed, so local cached observations expire.
                    pass
            raise

    def extend(self, values: Iterable[T]) -> None:
        pending = tuple(values)
        if pending:
            super().extend(pending)
            self._changed()

    @overload
    def __setitem__(self, key: SupportsIndex, value: T) -> None: ...

    @overload
    def __setitem__(self, key: slice, value: Iterable[T]) -> None: ...

    def __setitem__(self, key: SupportsIndex | slice, value: T | Iterable[T]) -> None:
        if isinstance(key, slice):
            super().__setitem__(key, cast(Iterable[T], value))
        else:
            super().__setitem__(key, cast(T, value))
        self._changed()

    def __delitem__(self, key: SupportsIndex | slice) -> None:
        if isinstance(key, slice):
            self.__setitem__(key, ())
        else:
            self.pop(key)

    def clear(self) -> None:
        if self:
            super().clear()
            self._changed()

    def insert(self, index: SupportsIndex, value: T) -> None:
        super().insert(as_index(index), value)
        self._changed()

    def pop(self, index: SupportsIndex = -1) -> T:
        result = super().pop(as_index(index))
        self._changed()
        return result

    def remove(self, value: T) -> None:
        super().remove(value)
        self._changed()

    def reverse(self) -> None:
        super().reverse()
        self._changed()

    def sort(self, *, key: object = None, reverse: bool = False) -> Never:
        raise TypeError("tracked retained lists do not support in-place sorting")

    def __iadd__(self, values: object) -> Never:
        raise TypeError("tracked retained lists do not support in-place addition")

    def __add__(self, values: object) -> Never:
        raise TypeError(
            "tracked retained lists do not expose concatenated backing lists"
        )

    def __imul__(self, count: SupportsIndex) -> Self:
        super().__imul__(count)
        self._changed()
        return self


class _StoreSerializationBoundary:
    __slots__ = ()

    def __reduce__(self) -> Never:
        raise TypeError("retained execution stores are not serializable")

    def __reduce_ex__(self, protocol: SupportsIndex) -> Never:
        raise TypeError("retained execution stores are not serializable")

    def __getstate__(self) -> Never:
        raise TypeError("retained execution stores are not serializable")


class LedgerDict(_StoreSerializationBoundary, MutableMapping[K, V]):
    __slots__ = ("_data", "_sealed", "ledger", "nodes_per_entry", "owner", "write_once")

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("retained store ownership is immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("retained store ownership cannot be deleted")

    def __init__(
        self,
        ledger: ResourceLedger,
        owner: int,
        nodes_per_entry: int,
        *,
        write_once: bool = False,
    ) -> None:
        if getattr(self, "_sealed", False):
            raise TypeError("retained stores cannot be reinitialized")
        self._data: dict[K, V] = TrackedDict(ledger)
        self.ledger, self.owner, self.nodes_per_entry = ledger, owner, nodes_per_entry
        self.write_once = write_once
        self._sealed = True

    def _check(self, size: int) -> None:
        if not self.ledger.is_factory_container(self):
            raise RuntimeError("retained stores require their ledger factory")
        self.ledger.check_store_capacity(self.owner, size, size * self.nodes_per_entry)

    def __getitem__(self, key: K) -> V:
        if self.write_once:
            self._check(len(self))
        return self._data[key]

    def __iter__(self) -> Iterator[K]:
        return iter(self._data)

    def __len__(self) -> int:
        return len(self._data)

    def items(self) -> ItemsView[K, V]:
        """Read backing pairs without rehashing adversarially mutated keys."""
        return self._data.items()

    def keys(self) -> KeysView[K]:
        return self._data.keys()

    def values(self) -> ValuesView[V]:
        return self._data.values()

    @property
    def sealed(self) -> bool:
        """Expose immutable initialization state to read-only auditors."""
        return self._sealed

    @property
    def backing_store(self) -> Mapping[K, V]:
        """Expose the exact backing identity through a read-only mapping view."""
        return self._data

    @property
    def backing_bytes(self) -> int:
        """Return the backing map's measured capacity from its owning wrapper."""
        from sys import getsizeof

        return getsizeof(self._data)

    def rollback_failed_write(
        self, key: K, attempted_value: V, restored_value: V
    ) -> None:
        """Restore one exact value after a mutation hook failed post-write.

        This is reserved for transaction cleanup. It does not change ledger
        reservations; the transaction owner remains responsible for those.
        """
        if not self.ledger.is_factory_container(self):
            raise RuntimeError("retained stores require their ledger factory")
        self._check(len(self))
        missing = object()
        current: object = self._data.get(key, missing)
        if current is missing:
            raise RuntimeError("failed-write rollback found no store value")
        if current is restored_value:
            return
        if current is not attempted_value:
            raise RuntimeError("failed-write rollback found another store value")
        dict[K, V].__setitem__(self._data, key, restored_value)
        try:
            self.ledger.note_store_mutation()
        except BaseException:
            # Preserve the publication failure while the backing store is
            # already restored; the ledger mutation generation is monotone.
            pass

    def rollback_inserted_value(self, key: K, expected_value: V) -> bool:
        """Remove one exact partial insertion without releasing its reservation."""
        if not self.ledger.is_factory_container(self):
            raise RuntimeError("retained stores require their ledger factory")
        self._check(len(self))
        return self._remove_exact_value(key, expected_value)

    def restore_deleted_value(self, key: K, value: V) -> None:
        """Restore one removed value after a transaction's mutation hook fails."""
        if not self.ledger.is_factory_container(self):
            raise RuntimeError("retained stores require their ledger factory")
        if self.write_once:
            raise TypeError("write-once mappings cannot restore a deleted value")
        self._check(len(self) + 1)
        if key in self._data:
            raise RuntimeError("store rollback found a replacement value")
        dict[K, V].__setitem__(self._data, key, value)
        try:
            self.ledger.note_store_mutation()
        except BaseException:
            # The owner is restoring state after another mutation failure. The
            # ledger generation has already been invalidated by that attempt.
            pass

    def _remove_exact_value(self, key: K, expected_value: V) -> bool:
        """Remove exactly one expected object while preserving its reservation."""
        sentinel = object()
        current: object = self._data.get(key, sentinel)
        if current is sentinel:
            return False
        if current is not expected_value:
            raise RuntimeError("store rollback found another object")
        dict[K, V].__delitem__(self._data, key)
        try:
            self.ledger.note_store_mutation()
        except BaseException:
            pass
        return True

    def __setitem__(self, key: K, value: V) -> None:
        if self.write_once and key in self._data:
            raise TypeError("canonical mapping entries are write-once")
        self._check(len(self) + int(key not in self))
        self._data[key] = value

    def rollback_unpublished(self, key: K, expected: V) -> bool:
        """Remove one exact object inserted by a failed publication transaction.

        Normal write-once mutation rules remain unchanged. The caller must
        still hold the reservation made before insertion; this method only
        releases that entry when the current value is the exact object it
        attempted to publish. It also handles a backing-store hook that raises
        after insertion but before ``__setitem__`` returns.
        """
        if not self.ledger.is_factory_container(self):
            raise RuntimeError("retained stores require their ledger factory")
        if not self.write_once:
            raise TypeError("unpublished rollback requires a write-once mapping")
        removed = self._remove_exact_value(key, expected)
        if not removed:
            return False
        self.ledger.release(self.owner, entries=1, nodes=self.nodes_per_entry)
        return True

    def __delitem__(self, key: K) -> None:
        if self.write_once:
            raise TypeError("canonical mapping entries cannot be deleted")
        self._check(len(self))
        del self._data[key]

    def clear(self) -> None:
        if self.write_once:
            raise TypeError("canonical mapping entries cannot be deleted")
        self._check(len(self))
        self._data.clear()

    @overload
    def update(self, other: _SupportsKeysAndGetItem[K, V], /) -> None: ...

    @overload
    def update(
        self,
        other: Iterable[tuple[K, V]],
        /,
    ) -> None: ...

    @overload
    def update(
        self: LedgerDict[str, V],
        other: _SupportsKeysAndGetItem[str, V],
        /,
        **kwargs: V,
    ) -> None: ...

    @overload
    def update(
        self: LedgerDict[str, V],
        other: Iterable[tuple[str, V]],
        /,
        **kwargs: V,
    ) -> None: ...

    @overload
    def update(self: LedgerDict[str, V], /, **kwargs: V) -> None: ...

    def update(
        self: _MappingUpdateTarget[UpdateK, UpdateV],
        other: _SupportsKeysAndGetItem[UpdateK, UpdateV]
        | Iterable[tuple[UpdateK, UpdateV]] = (),
        /,
        **kwargs: UpdateV,
    ) -> None:
        self.apply_update(dict[UpdateK, UpdateV](other, **kwargs))

    def apply_update(self, values: Mapping[K, V]) -> None:
        if self.write_once and any(key in self._data for key in values):
            raise TypeError("canonical mapping entries are write-once")
        self._check(len(self) + sum(key not in self for key in values))
        self._data.update(values)

    def __ior__(self, other: Mapping[K, V] | Iterable[tuple[K, V]]) -> LedgerDict[K, V]:
        self.update(other)
        return self


class LedgerList(_StoreSerializationBoundary, MutableSequence[T]):
    __slots__ = (
        "_data",
        "_sealed",
        "append_only",
        "ledger",
        "nodes_per_entry",
        "owner",
    )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("retained store ownership is immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("retained store ownership cannot be deleted")

    def __init__(
        self,
        ledger: ResourceLedger,
        owner: int,
        nodes_per_entry: int,
        append_only: bool,
    ) -> None:
        if getattr(self, "_sealed", False):
            raise TypeError("canonical arena identities cannot be reinitialized")
        self._data: _TrackedList[T] = _TrackedList(ledger)
        self.ledger, self.owner = ledger, owner
        self.nodes_per_entry, self.append_only = nodes_per_entry, append_only
        self._sealed = True

    def _check(self, size: int) -> None:
        if not self.ledger.is_factory_container(self):
            raise RuntimeError("retained stores require their ledger factory")
        self.ledger.check_store_capacity(self.owner, size, size * self.nodes_per_entry)

    def _editable(self) -> None:
        if self.append_only:
            raise TypeError(
                "canonical arena identities are append-only and cannot be recycled"
            )

    def rollback_unpublished(self, size: int) -> None:
        """Remove a journaled unpublished suffix without recycling a live ID.

        This checked transaction operation is for an owner that reserved and
        journaled the suffix before publication. It does not authorize reuse of
        any ID whose value escaped to a consumer.
        """
        if type(size) is not int or not 0 <= size <= len(self._data):
            raise ValueError("unpublished rollback requires a valid prior size")
        if size < len(self._data):
            del self._data[size:]

    def __len__(self) -> int:
        return len(self._data)

    @property
    def backing_size_bytes(self) -> int:
        """Report the exact backing-list allocation without exposing it."""
        return getsizeof(self._data)

    def __iter__(self) -> Iterator[T]:
        # A native list_iterator exposes its backing list through __reduce__.
        # Iterate public indices so no iterator can hand out the identity store.
        index = 0
        while index < len(self):
            yield self[index]
            index += 1

    def snapshot(self) -> tuple[T, ...]:
        """Copy values without exposing a reducible backing-list iterator.

        This is an immutable, detached value snapshot, not retained authority.
        Native tuple construction avoids a Python callback for every element;
        ordinary public iteration keeps its non-serializable boundary above.
        """
        return tuple(self._data)

    @property
    def backing_bytes(self) -> int:
        """Return measured list capacity without exposing the backing list."""
        from sys import getsizeof

        return getsizeof(self._data)

    @property
    def mutation_stamp(self) -> tuple[object, int]:
        """Opaque backing authority and revision, without exposing its values.

        Direct adversarial backing-list mutators invalidate this stamp as well
        as the ledger-wide audit revision. Unrelated stores do not invalidate
        a consumer's checked prefix of this sequence.
        """
        return self._data.mutation_stamp

    @overload
    def __getitem__(self, key: SupportsIndex) -> T: ...
    @overload
    def __getitem__(self, key: slice) -> list[T]: ...
    def __getitem__(self, key: SupportsIndex | slice) -> T | list[T]:
        return self._data[key]

    def _equality_backing(self) -> object:
        """Borrow the list backing through an element-type-independent view."""
        return self._data

    def __eq__(self, other: object) -> bool:
        return self._data == (
            other._equality_backing() if isinstance(other, LedgerList) else other
        )

    def append(self, value: T) -> None:
        self._check(len(self) + 1)
        self._data.append(value)

    def extend(self, values: Iterable[T]) -> None:
        pending = tuple(values)
        self._check(len(self) + len(pending))
        self._data.extend(pending)

    def __iadd__(self, values: Iterable[T]) -> LedgerList[T]:
        self.extend(values)
        return self

    def __imul__(self, count: SupportsIndex) -> LedgerList[T]:
        self._editable()
        self._check(len(self) * max(0, as_index(count)))
        self._data.__imul__(count)
        return self

    @overload
    def __setitem__(self, key: SupportsIndex, value: T) -> None: ...
    @overload
    def __setitem__(self, key: slice, value: Iterable[T]) -> None: ...
    def __setitem__(self, key: SupportsIndex | slice, value: T | Iterable[T]) -> None:
        self._editable()
        if isinstance(key, slice):
            if not isinstance(value, Iterable):
                raise TypeError("slice assignment requires an iterable")
            pending = tuple(cast(Iterable[T], value))
            self._check(len(self) - len(self[key]) + len(pending))
            self._data[key] = pending
        else:
            self._check(len(self))
            self._data[key] = cast(T, value)

    def __delitem__(self, key: SupportsIndex | slice) -> None:
        self._editable()
        self._check(len(self))
        del self._data[key]

    def insert(self, index: SupportsIndex, value: T) -> None:
        self._editable()
        self._check(len(self) + 1)
        self._data.insert(index, value)

    def pop(self, index: int = -1) -> T:
        self._editable()
        self._check(len(self))
        return self._data.pop(index)

    def remove(self, value: T) -> None:
        self._editable()
        self._check(len(self))
        self._data.remove(value)

    def clear(self) -> None:
        self._editable()
        self._check(len(self))
        self._data.clear()

    def reverse(self) -> None:
        self._editable()
        self._check(len(self))
        self._data.reverse()

    def sort(self, *, key: object = None, reverse: bool = False) -> None:
        self._editable()
        raise TypeError("sorting retained identity stores is unsupported")


def append_indexed_node(
    ledger: ResourceLedger,
    nodes: MutableSequence[T],
    keys: MutableMapping[K, int],
    node_owner: int,
    key_owner: int,
    key: K,
    record: T,
    *,
    reservations: tuple[tuple[int, int, int], ...] = (),
) -> int:
    """Reserve and append one already-admitted dense arena node and its index.

    Semantic validation and hit detection belong to the caller. Both retained
    stores remain ledger-created; this does not grant unscoped handle authority.
    """
    ledger.reserve_many(((node_owner, 1, 1), (key_owner, 1, 0), *reservations))
    local_id = len(nodes)
    nodes.append(record)
    keys[key] = local_id
    return local_id


def reserve_indexed_id(
    ledger: ResourceLedger, node_owner: int, key_owner: int, next_id: int
) -> tuple[int, int]:
    """Admit one monotone arena identity before the caller mutates either index."""
    ledger.reserve_many(((node_owner, 1, 1), (key_owner, 1, 0)))
    return next_id, next_id + 1


class NodeIndexFactory(Generic[NodeT, NodeKeyT]):
    """Typed constructors for the two canonical ledgered arena index shapes."""

    @staticmethod
    def dense(
        ledger: ResourceLedger,
        node_owner: int,
        key_owner: int,
    ) -> tuple[LedgerList[NodeT], LedgerDict[NodeKeyT, int]]:
        """Create an append-only node sequence and its entry-only reverse index."""
        nodes: LedgerList[NodeT] = ledger.make_list(node_owner)
        keys: LedgerDict[NodeKeyT, int] = ledger.make_dict(key_owner)
        ledger.register_container(
            node_owner, nodes, node_count=lambda: len(nodes), payloads=lambda: nodes
        )
        ledger.register_container(key_owner, keys, payloads=keys.items)
        return nodes, keys

    @staticmethod
    def sparse(
        ledger: ResourceLedger,
        node_owner: int,
        key_owner: int,
    ) -> tuple[LedgerDict[int, NodeT], LedgerDict[NodeKeyT, int]]:
        """Create a node-counted sparse map and an entry-only semantic index."""
        nodes: LedgerDict[int, NodeT] = ledger.make_dict(node_owner, nodes_per_entry=1)
        keys: LedgerDict[NodeKeyT, int] = ledger.make_dict(key_owner)
        ledger.register_container(
            node_owner,
            nodes,
            node_count=lambda: len(nodes),
            payloads=nodes.items,
        )
        ledger.register_container(key_owner, keys, payloads=keys.items)
        return nodes, keys


def record_indexed_node(
    nodes: MutableMapping[int, T],
    keys: MutableMapping[T, int],
    local_id: int,
    record: T,
) -> None:
    """Install an admitted sparse node and its matching semantic reverse index."""
    nodes[local_id] = record
    keys[record] = local_id
