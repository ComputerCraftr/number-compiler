"""Private source bindings for protected double-reversal bank records."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from copy import deepcopy
from dataclasses import fields, is_dataclass
from types import MappingProxyType
from typing import Generic, TypeGuard, TypeVar, cast
from weakref import ReferenceType, ref

from number_compiler.arithmetic.automata.slp import SLPArena

_Key = TypeVar("_Key")
_Value = TypeVar("_Value")
_Record = TypeVar("_Record", bound="SourceAuthorizedRecord")
_AUTHORITY_SEAL = object()
_MAX_SNAPSHOT_WORK = 1_000_000


def _is_object_mapping(value: object) -> TypeGuard[Mapping[object, object]]:
    """Narrow an inspected packet mapping to read-only object values."""
    return isinstance(value, Mapping)


def _is_object_sequence(
    value: object,
) -> TypeGuard[tuple[object, ...] | list[object]]:
    return isinstance(value, (tuple, list))


def _is_object_set(value: object) -> TypeGuard[set[object] | frozenset[object]]:
    return isinstance(value, (set, frozenset))


def _supported_packet_shape(value: object) -> bool:
    return (
        _is_object_mapping(value)
        or _is_object_sequence(value)
        or _is_object_set(value)
        or (is_dataclass(value) and not isinstance(value, type))
    )


def _is_source_authorized_record(
    value: object,
) -> TypeGuard[SourceAuthorizedRecord]:
    return isinstance(value, SourceAuthorizedRecord)


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


class SourceAuthorizedRecord:
    """Dataclass base whose authority slot is deliberately absent from fields."""

    __slots__ = ("_source_authority",)


class SourceRecordAuthority:
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
        record: SourceAuthorizedRecord,
        parent: SourceRecordAuthority | None,
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


def snapshot_value(value: object) -> object:
    """Freeze packet graphs to a flat, typed, cycle-free representation."""
    scalar_types = (bool, int, str, bytes, type(None))
    # Container children are node references, so snapshot comparison remains
    # shallow even when a supported packet is deeply nested.
    tasks: list[tuple[str, object, object]] = [("visit", value, None)]
    values: list[object] = []
    active: set[int] = set()
    node_indices: dict[int, int] = {}
    nodes: list[object | None] = []
    work = 0
    while tasks:
        operation, subject, metadata = tasks.pop()
        work += 1
        if work > _MAX_SNAPSHOT_WORK:
            raise ValueError("temporal packet snapshot exceeds its work budget")
        if operation == "visit":
            current = subject
            if type(current) in scalar_types:
                values.append(("scalar", type(current), current))
                continue
            if not _supported_packet_shape(current):
                raise TypeError("temporal packet contains an unsupported value shape")
            identity = id(current)
            if identity in active:
                raise ValueError("temporal packet contains a cycle")
            if identity in node_indices:
                values.append(("node", node_indices[identity]))
                continue
            if _is_object_mapping(current):
                if 2 * len(current) > _MAX_SNAPSHOT_WORK - work:
                    raise ValueError("temporal packet snapshot exceeds its work budget")
                children: list[object] = [
                    part for pair in current.items() for part in pair
                ]
                kind = "mapping"
                descriptor: object = len(children) // 2
            elif is_dataclass(current) and not isinstance(current, type):
                members = fields(current)
                children = [getattr(current, member.name) for member in members]
                kind = "dataclass"
                descriptor = tuple(member.name for member in members)
            elif _is_object_set(current):
                if len(current) > _MAX_SNAPSHOT_WORK - work:
                    raise ValueError("temporal packet snapshot exceeds its work budget")
                children = list(current)
                kind = "set"
                descriptor = len(children)
            elif _is_object_sequence(current):
                if len(current) > _MAX_SNAPSHOT_WORK - work:
                    raise ValueError("temporal packet snapshot exceeds its work budget")
                children = list(current)
                kind = "sequence"
                descriptor = len(children)
            else:
                raise TypeError("temporal packet contains an unsupported value shape")
            if len(children) > _MAX_SNAPSHOT_WORK - work:
                raise ValueError("temporal packet snapshot exceeds its work budget")
            node_index = len(nodes)
            node_indices[identity] = node_index
            nodes.append(None)
            active.add(identity)
            tasks.append(
                (
                    "exit",
                    identity,
                    (node_index, kind, len(values), (descriptor, type(current))),
                )
            )
            tasks.extend(("visit", child, None) for child in reversed(children))
            continue

        identity = cast(int, subject)
        node_index, kind, start, exit_metadata = cast(
            tuple[int, str, int, object], metadata
        )
        descriptor, concrete_type = cast(tuple[object, type[object]], exit_metadata)
        children = values[start:]
        del values[start:]
        if kind == "dataclass":
            names = cast(tuple[str, ...], descriptor)
            if len(names) != len(children):
                raise AssertionError("dataclass snapshot field count changed")
        elif kind == "mapping" and len(children) != 2 * cast(int, descriptor):
            raise AssertionError("mapping snapshot item count changed")
        nodes[node_index] = (kind, concrete_type, descriptor, tuple(children))
        active.remove(identity)
        values.append(("node", node_index))
    if len(values) != 1:
        raise AssertionError("temporal packet snapshot stack is inconsistent")
    if any(node is None for node in nodes):
        raise AssertionError("temporal packet snapshot has an unfinished node")
    return ("snapshot", values[0], tuple(nodes))


def _public_snapshot(record: SourceAuthorizedRecord) -> tuple[object, ...]:
    if not is_dataclass(record):
        raise TypeError("source authority requires a dataclass record")
    return tuple(
        (field.name, snapshot_value(getattr(record, field.name)))
        for field in fields(record)
    )


def issue_source_record(
    record: _Record,
    arena: SLPArena,
    root: int,
    *,
    parent: SourceRecordAuthority | None = None,
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
    authority = SourceRecordAuthority(
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


def validate_source_record(record: object) -> SourceRecordAuthority:
    """Reject direct construction, mutation, and cross-root packet reuse."""
    if not isinstance(record, SourceAuthorizedRecord):
        raise TypeError("temporal packet has no source authority")
    authority = getattr(record, "_source_authority", None)
    if (
        not isinstance(authority, SourceRecordAuthority)
        or authority.record is not record
    ):
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
            or not _is_source_authorized_record(current.record)
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


def require_same_source(
    first: SourceRecordAuthority, second: SourceRecordAuthority
) -> None:
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


def require_source_arena(authority: SourceRecordAuthority) -> SLPArena:
    """Return the still-live arena of a previously validated authority."""
    arena = authority.arena
    if arena is None:
        raise ValueError("temporal packet source arena is no longer available")
    return arena


__all__ = [
    "FrozenMap",
    "SourceRecordAuthority",
    "issue_source_record",
    "require_same_source",
    "require_source_arena",
    "validate_source_record",
]
