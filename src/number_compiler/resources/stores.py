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
from typing import TYPE_CHECKING, Never, Self, SupportsIndex, TypeVar, cast, overload

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


K = TypeVar("K")
V = TypeVar("V")
T = TypeVar("T")


class _TrackedDict(dict[K, V]):
    """Backing map that invalidates audits even through adversarial test access."""

    def __init__(self, ledger: ResourceLedger) -> None:
        super().__init__()
        self._ledger = ledger

    def __setitem__(self, key: K, value: V) -> None:
        super().__setitem__(key, value)
        self._ledger.note_store_mutation()

    def __delitem__(self, key: K) -> None:
        super().__delitem__(key)
        self._ledger.note_store_mutation()

    def clear(self) -> None:
        if self:
            super().clear()
            self._ledger.note_store_mutation()

    def setdefault(self, key: K, default: V | None = None) -> V:
        if key in self:
            return self[key]
        result = super().setdefault(key, cast(V, default))
        self._ledger.note_store_mutation()
        return result

    def update(self, *args: object, **kwargs: V) -> None:
        if len(args) > 1:
            raise TypeError("update accepts at most one positional mapping")
        values: dict[K, V] = {}
        if args:
            source = args[0]
            if isinstance(source, (Mapping, Iterable)):
                values.update(source)
            else:
                raise TypeError("update requires a mapping or key-value pairs")
        for name, value in kwargs.items():
            values[cast(K, name)] = value
        if values:
            super().update(values)
            self._ledger.note_store_mutation()


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

    def append(self, value: T) -> None:
        super().append(value)
        self._changed()

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
        super().__delitem__(key)
        self._changed()

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
        self._data: dict[K, V] = _TrackedDict(ledger)
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

    def __setitem__(self, key: K, value: V) -> None:
        if self.write_once and key in self._data:
            raise TypeError("canonical mapping entries are write-once")
        self._check(len(self) + int(key not in self))
        self._data[key] = value

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
    def setdefault(self, key: K, default: V, /) -> V: ...
    @overload
    def setdefault(
        self: LedgerDict[K, V | None], key: K, default: None = None, /
    ) -> V | None: ...
    def setdefault(self, key: K, default: V | None = None, /) -> V | None:
        if key in self:
            return self[key]
        self._check(len(self) + 1)
        return self._data.setdefault(key, cast(V, default))

    def update(self, *args: object, **kwargs: V) -> None:
        if len(args) > 1:
            raise TypeError("update accepts at most one positional mapping")
        values: dict[K, V] = {}
        if args:
            source = args[0]
            if isinstance(source, (Mapping, Iterable)):
                values.update(source)
            else:
                raise TypeError("update requires a mapping or key-value pairs")
        for name, value in kwargs.items():
            values[cast(K, name)] = value
        if self.write_once and any(key in self._data for key in values):
            raise TypeError("canonical mapping entries are write-once")
        self._check(len(self) + sum(key not in self for key in values))
        self._data.update(values)

    def __ior__(self, other: object) -> LedgerDict[K, V]:
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

    def _rollback_unpublished(self, size: int) -> None:
        """Remove a journaled unpublished suffix without recycling a live ID."""
        if type(size) is not int or not 0 <= size <= len(self._data):
            raise ValueError("unpublished rollback requires a valid prior size")
        if size < len(self._data):
            del self._data[size:]

    def __len__(self) -> int:
        return len(self._data)

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
    def mutation_stamp(self) -> tuple[object, int]:
        """Opaque backing authority and revision, without exposing its values.

        Direct adversarial backing-list mutators invalidate this stamp as well
        as the ledger-wide audit revision. Unrelated stores do not invalidate
        a consumer's checked prefix of this sequence.
        """
        return self._data._mutation_identity, self._data._mutation_version

    @overload
    def __getitem__(self, key: SupportsIndex) -> T: ...
    @overload
    def __getitem__(self, key: slice) -> list[T]: ...
    def __getitem__(self, key: SupportsIndex | slice) -> T | list[T]:
        return self._data[key]

    def __eq__(self, other: object) -> bool:
        return self._data == (other._data if isinstance(other, LedgerList) else other)

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
            pending = tuple(value)
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
