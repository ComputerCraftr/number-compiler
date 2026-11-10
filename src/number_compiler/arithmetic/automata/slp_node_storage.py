"""Mutation-aware node storage for standalone SLP arenas."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator, MutableSequence
from operator import index as as_index
from typing import Generic, Never, SupportsIndex, TypeVar, cast, overload

_NodeT = TypeVar("_NodeT")


class SLPNodeStorage(MutableSequence[_NodeT], Generic[_NodeT]):
    """A guarded sequence whose backing list is not exposed as the sequence."""

    __slots__ = ("_invalidate_node_ids", "_rows")

    def __init__(self, invalidate_node_ids: Callable[[], None]) -> None:
        self._rows: list[_NodeT] = []
        self._invalidate_node_ids = invalidate_node_ids

    @overload
    def __getitem__(self, key: SupportsIndex) -> _NodeT: ...

    @overload
    def __getitem__(self, key: slice) -> list[_NodeT]: ...

    def __getitem__(self, key: SupportsIndex | slice) -> _NodeT | list[_NodeT]:
        return self._rows[key]

    @overload
    def __setitem__(self, key: SupportsIndex, value: _NodeT) -> None: ...

    @overload
    def __setitem__(self, key: slice, value: Iterable[_NodeT]) -> None: ...

    def __setitem__(
        self, key: SupportsIndex | slice, value: _NodeT | Iterable[_NodeT]
    ) -> None:
        self._invalidate_node_ids()
        if isinstance(key, slice):
            self._rows[key] = cast(Iterable[_NodeT], value)
        else:
            self._rows[key] = cast(_NodeT, value)

    def __delitem__(self, key: SupportsIndex | slice) -> None:
        self._invalidate_node_ids()
        del self._rows[key]

    def __len__(self) -> int:
        return len(self._rows)

    def __iter__(self) -> Iterator[_NodeT]:
        return iter(self._rows)

    def insert(self, index: SupportsIndex, value: _NodeT) -> None:
        self._invalidate_node_ids()
        self._rows.insert(as_index(index), value)

    def append(self, value: _NodeT) -> None:
        self._rows.append(value)

    def extend(self, values: Iterable[_NodeT]) -> None:
        self._rows.extend(self._rows.copy() if values is self else values)

    def __iadd__(self, values: Iterable[_NodeT]) -> SLPNodeStorage[_NodeT]:
        self.extend(values)
        return self

    def __imul__(self, count: SupportsIndex) -> SLPNodeStorage[_NodeT]:
        repetitions = as_index(count)
        if self._rows and repetitions != 1:
            self._invalidate_node_ids()
        self._rows *= repetitions
        return self

    def pop(self, index: SupportsIndex = -1) -> _NodeT:
        self._invalidate_node_ids()
        return self._rows.pop(as_index(index))

    def remove(self, value: _NodeT) -> None:
        self._invalidate_node_ids()
        self._rows.remove(value)

    def clear(self) -> None:
        if self._rows:
            self._invalidate_node_ids()
            self._rows.clear()

    def reverse(self) -> None:
        if len(self._rows) > 1:
            self._invalidate_node_ids()
            self._rows.reverse()

    def sort(self, *, key: object = None, reverse: bool = False) -> Never:
        raise TypeError("sorting identity-bearing SLP node storage is unsupported")

    def __eq__(self, other: object) -> bool:
        if isinstance(other, SLPNodeStorage):
            other = cast("SLPNodeStorage[object]", other)._rows
        return self._rows == other

    def __repr__(self) -> str:
        return repr(self._rows)
