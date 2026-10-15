"""Private source bindings for protected double-reversal bank records."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from copy import deepcopy
from dataclasses import fields, is_dataclass
from types import MappingProxyType
from typing import Generic, TypeVar
from weakref import ReferenceType, ref

from number_compiler.arithmetic.automata.slp import SLPArena

_Key = TypeVar("_Key")
_Value = TypeVar("_Value")
_Record = TypeVar("_Record", bound="_SourceAuthorizedRecord")
_AUTHORITY_SEAL = object()


class FrozenMap(Mapping[_Key, _Value], Generic[_Key, _Value]):
    """Dict-shaped immutable packet map with an ``asdict`` wire copy."""

    __slots__ = ("_values",)

    def __init__(self, values: Mapping[_Key, _Value]) -> None:
        self._values = MappingProxyType(dict(values))

    def __getitem__(self, key: _Key) -> _Value:
        return self._values[key]

    def __iter__(self) -> Iterator[_Key]:
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)

    def __deepcopy__(self, memo: dict[int, object]) -> dict[_Key, _Value]:
        copied = deepcopy(dict(self._values), memo)
        return copied


class _SourceAuthorizedRecord:
    """Dataclass base whose authority slot is deliberately absent from fields."""

    __slots__ = ("_source_authority",)


class _SourceAuthority:
    __slots__ = (
        "_arena_ref",
        "_arena_strong",
        "parent",
        "record",
        "root",
        "root_node",
        "seal",
        "snapshot",
        "source_generation",
    )

    def __init__(
        self,
        *,
        arena: SLPArena,
        root: int,
        root_node: object,
        record: _SourceAuthorizedRecord,
        parent: _SourceAuthority | None,
        source_generation: int,
        snapshot: tuple[object, ...],
    ) -> None:
        self.seal = _AUTHORITY_SEAL
        try:
            self._arena_ref: ReferenceType[SLPArena] | None = ref(arena)
            self._arena_strong: SLPArena | None = None
        except TypeError:
            self._arena_ref = None
            self._arena_strong = arena
        self.root = root
        self.root_node = root_node
        self.record = record
        self.parent = parent
        self.snapshot = snapshot
        self.source_generation = source_generation

    @property
    def arena(self) -> SLPArena | None:
        return self._arena_strong if self._arena_ref is None else self._arena_ref()


def _snapshot_value(value: object) -> object:
    if isinstance(value, Mapping):
        return tuple(sorted(value.items(), key=lambda pair: repr(pair[0])))
    if (
        isinstance(value, tuple)
        and value
        and is_dataclass(value[0])
        and not isinstance(value[0], type)
    ):
        return tuple(
            tuple(getattr(item, field.name) for field in fields(item)) for item in value
        )
    return value


def _public_snapshot(record: _SourceAuthorizedRecord) -> tuple[object, ...]:
    if not is_dataclass(record):
        raise TypeError("source authority requires a dataclass record")
    return tuple(
        (field.name, _snapshot_value(getattr(record, field.name)))
        for field in fields(record)
    )


def issue_source_record(
    record: _Record,
    arena: SLPArena,
    root: int,
    *,
    parent: _SourceAuthority | None = None,
    source_generation: int = 0,
) -> _Record:
    """Bind an immutable packet to the exact source root and public snapshot."""
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("source authority root is invalid")
    if type(source_generation) is not int or source_generation < 0:
        raise ValueError("source generation must be nonnegative")
    if parent is not None:
        validate_source_record(parent.record)
        if (
            parent.arena is not arena
            or parent.root != root
            or parent.source_generation != source_generation
        ):
            raise ValueError("child packet source differs from its authority parent")
    authority = _SourceAuthority(
        arena=arena,
        root=root,
        root_node=arena.nodes[root],
        record=record,
        parent=parent,
        source_generation=source_generation,
        snapshot=_public_snapshot(record),
    )
    object.__setattr__(record, "_source_authority", authority)
    return record


def validate_source_record(record: object) -> _SourceAuthority:
    """Reject direct construction, mutation, and cross-root packet reuse."""
    if not isinstance(record, _SourceAuthorizedRecord):
        raise TypeError("temporal packet has no source authority")
    authority = getattr(record, "_source_authority", None)
    if not isinstance(authority, _SourceAuthority) or authority.record is not record:
        raise ValueError("temporal packet source authority is invalid")
    pending = [authority]
    visited: set[int] = set()
    while pending:
        current = pending.pop()
        if id(current) in visited:
            continue
        visited.add(id(current))
        arena = current.arena
        if (
            current.seal is not _AUTHORITY_SEAL
            or not isinstance(current.record, _SourceAuthorizedRecord)
            or arena is None
            or not 0 <= current.root < len(arena.nodes)
            or arena.nodes[current.root] is not current.root_node
            or _public_snapshot(current.record) != current.snapshot
        ):
            raise ValueError("temporal packet source authority is invalid")
        if current.parent is not None:
            parent = current.parent
            if parent.arena is not arena or parent.root != current.root:
                raise ValueError("temporal packet authority parent changed source")
            if parent.source_generation != current.source_generation:
                raise ValueError("temporal packet owner generation changed")
            pending.append(parent)
    return authority


def require_same_source(first: _SourceAuthority, second: _SourceAuthority) -> None:
    """Require exact arena/root identity, not equal width or prefix metadata."""
    if (
        first.arena is None
        or second.arena is None
        or first.arena is not second.arena
        or first.root != second.root
        or first.root_node is not second.root_node
        or first.source_generation != second.source_generation
    ):
        raise ValueError("temporal packets have different source roots or generations")


__all__ = [
    "FrozenMap",
    "issue_source_record",
    "require_same_source",
    "validate_source_record",
]
