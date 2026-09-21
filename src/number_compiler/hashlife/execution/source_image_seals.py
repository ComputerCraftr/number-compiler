"""Independent integrity seals for scheduler-owned immutable publications."""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import fields, is_dataclass
from typing import Self, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

_FieldAnchor = tuple[type[object], object | None]
_Guard = tuple[object, type[object], tuple[str, ...], tuple[_FieldAnchor, ...]]


def _primitive(value: object) -> bool:
    return value is None or type(value) in (bool, int, str, bytes)


def _anchor(value: object) -> _FieldAnchor:
    # Retaining the object prevents Python from recycling its identity after a
    # reflected field replacement. The exact type already determines whether
    # this is a primitive value comparison or an identity comparison.
    return (type(value), value)


def _anchor_matches(value: object, expected: _FieldAnchor) -> bool:
    expected_type, expected_value = expected
    if type(value) is not expected_type:
        return False
    return value == expected_value if _primitive(value) else value is expected_value


def _root_anchor(value: object) -> object:
    if type(value) is tuple:
        return (
            "tuple",
            tuple(_anchor(item) for item in cast(tuple[object, ...], value)),
        )
    if type(value) is frozenset:
        return ("frozenset", value)
    return _anchor(value)


def _root_matches(value: object, expected: object) -> bool:
    if type(value) is tuple:
        if type(expected) is not tuple or len(expected) != 2 or expected[0] != "tuple":
            return False
        children = cast(tuple[object, ...], value)
        anchors = expected[1]
        return (
            type(anchors) is tuple
            and len(children) == len(anchors)
            and all(
                _anchor_matches(child, anchor)
                for child, anchor in zip(children, anchors)
            )
        )
    if type(value) is frozenset:
        return (
            type(expected) is tuple
            and len(expected) == 2
            and expected[0] == "frozenset"
            and expected[1] is value
        )
    return type(expected) is tuple and _anchor_matches(
        value, cast(_FieldAnchor, expected)
    )


class PublicationSeal(tuple[object, tuple[_Guard, ...], int]):
    """Exact process-local anchors for one immutable publication graph."""

    __slots__ = ()

    def __new__(
        cls, root: object, guards: tuple[_Guard, ...], retained_nodes: int
    ) -> Self:
        # Keep tuple immutability without NamedTuple's mutable class-level
        # defaults dictionary entering every retained execution graph.
        return tuple.__new__(cls, (root, guards, retained_nodes))

    @property
    def root(self) -> object:
        return self[0]

    @property
    def guards(self) -> tuple[_Guard, ...]:
        return self[1]

    @property
    def retained_nodes(self) -> int:
        return self[2]


class PublicationSeals:
    """Ledger-owned seal authority kept outside the records it authenticates."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self._image_owner = ledger.register(
            prefix + "-image-seals", "source_image_publication_seal"
        )
        self._projection_owner = ledger.register(
            prefix + "-projection-seals", "source_image_publication_seal"
        )
        self.images: LedgerList[PublicationSeal] = ledger.make_list(
            self._image_owner, nodes_per_entry=0, append_only=False
        )
        self.projections: LedgerDict[Hashable, PublicationSeal] = ledger.make_dict(
            self._projection_owner
        )
        ledger.register_container(
            self._image_owner,
            self.images,
            node_count=lambda: sum(item.retained_nodes for item in self.images),
            payloads=self.images.__iter__,
        )
        ledger.register_container(
            self._projection_owner,
            self.projections,
            node_count=lambda: sum(
                item.retained_nodes for item in self.projections.values()
            ),
            payloads=self.projections.items,
        )

    def append_image(self, seal: PublicationSeal) -> None:
        self.ledger.reserve(self._image_owner, entries=1, nodes=seal.retained_nodes)
        try:
            self.images.append(seal)
        except BaseException:
            self.ledger.release(self._image_owner, entries=1, nodes=seal.retained_nodes)
            raise

    def pop_image(self) -> PublicationSeal:
        seal = self.images.pop()
        self.ledger.release(self._image_owner, entries=1, nodes=seal.retained_nodes)
        return seal

    def put_projection(self, key: Hashable, seal: PublicationSeal) -> None:
        if key in self.projections:
            raise ValueError("source image projection seal was already published")
        self.ledger.reserve(
            self._projection_owner, entries=1, nodes=seal.retained_nodes
        )
        try:
            self.projections[key] = seal
        except BaseException:
            self.ledger.release(
                self._projection_owner, entries=1, nodes=seal.retained_nodes
            )
            raise

    def drop_projection(self, key: Hashable) -> None:
        seal = self.projections.pop(key)
        self.ledger.release(
            self._projection_owner, entries=1, nodes=seal.retained_nodes
        )

    def clear(self) -> None:
        image_nodes = sum(item.retained_nodes for item in self.images)
        projection_nodes = sum(
            item.retained_nodes for item in self.projections.values()
        )
        image_count, projection_count = len(self.images), len(self.projections)
        self.images.clear()
        self.projections.clear()
        self.ledger.release(self._image_owner, entries=image_count, nodes=image_nodes)
        self.ledger.release(
            self._projection_owner,
            entries=projection_count,
            nodes=projection_nodes,
        )


def publication_seal(value: object, ledger: ResourceLedger) -> PublicationSeal:
    """Capture every mutable-via-reflection object once, without hash authority.

    Tuples and frozensets cannot change in place, so the seal retains their identity
    and traverses them only at publication time to find nested dataclasses. Each
    dataclass or arena handle retains an independent shallow field snapshot. Warm
    validation visits guarded objects instead of flattening large primitive tuples.
    """
    root_nodes = 3 + (1 + 2 * len(value) if type(value) is tuple else 0)
    retained_nodes = 4 + root_nodes
    ledger.check_capacity(nodes=retained_nodes)
    pending: list[tuple[object, bool]] = [(value, False)]
    active: set[int] = set()
    finished: set[int] = set()
    guards: list[_Guard] = []
    visits = consumed = 0
    try:
        while pending:
            current, leaving = pending.pop()
            identity = id(current)
            if leaving:
                active.remove(identity)
                finished.add(identity)
                continue
            visits += 1
            if _primitive(current):
                if type(current) is int:
                    consumed += max(1, (abs(current).bit_length() + 7) // 8)
                elif type(current) is str:
                    consumed += len(current.encode("utf-8"))
                elif type(current) is bytes:
                    consumed += len(current)
                continue
            if identity in active:
                raise ValueError("publication contains a reference cycle")
            if identity in finished:
                continue
            children: tuple[object, ...]
            if isinstance(current, ArenaHandle):
                retained_nodes += 14
                ledger.check_capacity(nodes=retained_nodes)
                guards.append(
                    (
                        current,
                        type(current),
                        ("owner", "kind", "local_id"),
                        (
                            _anchor(current.owner),
                            _anchor(current.kind),
                            _anchor(current.local_id),
                        ),
                    )
                )
                # Arena authority is identity-anchored and is not traversed.
                children = (current.kind, current.local_id)
            elif type(current) in (tuple, frozenset):
                children = tuple(cast(tuple[object, ...] | frozenset[object], current))
            elif is_dataclass(current) and not isinstance(current, type):
                names = tuple(item.name for item in fields(current))
                children = tuple(getattr(current, name) for name in names)
                retained_nodes += 5 + 3 * len(names)
                ledger.check_capacity(nodes=retained_nodes)
                guards.append(
                    (
                        current,
                        type(current),
                        names,
                        tuple(_anchor(child) for child in children),
                    )
                )
            else:
                raise TypeError("publication contains an unsupported value")
            ledger.check_capacity(nodes=retained_nodes + len(pending) + len(children))
            active.add(identity)
            pending.append((current, True))
            pending.extend((child, False) for child in reversed(children))
            consumed += 8 + 8 * len(children)
        return PublicationSeal(_root_anchor(value), tuple(guards), retained_nodes)
    finally:
        ledger.bump("source_image_seal_creation_visits", visits)
        ledger.bump("source_image_seal_creation_bytes", consumed)
        # Preserve aggregate counters consumed by existing reporting.
        ledger.bump("source_image_seal_visits", visits)
        ledger.bump("source_image_seal_bytes", consumed)


def _publication_matches(value: object, seal: PublicationSeal) -> tuple[bool, int]:
    visits = 1
    valid = type(seal) is PublicationSeal and _root_matches(value, seal.root)
    if valid:
        for current, expected_type, names, expected in seal.guards:
            visits += 1
            if type(current) is not expected_type:
                valid = False
                break
            if any(
                not _anchor_matches(value, anchor)
                for value, anchor in zip(
                    (getattr(current, name) for name in names),
                    expected,
                )
            ):
                valid = False
                break
    return valid, visits


def publication_matches(
    value: object, seal: PublicationSeal, ledger: ResourceLedger
) -> bool:
    """Validate exact root and field anchors and charge the runtime visit."""
    valid, visits = _publication_matches(value, seal)
    ledger.bump("source_image_seal_validation_visits", visits)
    return valid


def publication_matches_readonly(value: object, seal: PublicationSeal) -> bool:
    """Validate the same independent anchors without changing runtime metrics."""
    return _publication_matches(value, seal)[0]


__all__ = [
    "PublicationSeal",
    "publication_matches",
    "publication_matches_readonly",
    "publication_seal",
]
