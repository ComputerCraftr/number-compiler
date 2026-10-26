"""Independent integrity seals for scheduler-owned immutable publications."""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass, fields, is_dataclass
from typing import Generic, Protocol, Self, TypeVar, cast

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.exact_equality import (
    extend_typed_tuple_pairs,
)
from number_compiler.arithmetic.contracts.iterative_queries import (
    enter_ordered_children,
    enter_tuple_node,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.stores import LedgerDict, LedgerList

_FieldAnchor = tuple[type[object], object | None]
_Guard = tuple[object, type[object], tuple[str, ...], tuple[object, ...]]
NodeT = TypeVar("NodeT")


class SourceImageIndexRollback(Protocol):
    def __call__(self) -> None: ...


def _primitive(value: object) -> bool:
    return value is None or type(value) in (
        bool,
        int,
        str,
        bytes,
        ActionTransform,
    )


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


def _guard_field_matches(
    value: object, expected_type: type[object], expected: object
) -> bool:
    """Compare a field against its separately pinned original type and value."""
    if type(value) is not expected_type:
        return False
    return value == expected if _primitive(expected) else value is expected


def _root_anchor(value: object) -> object:
    if type(value) is tuple:
        return (
            "tuple",
            tuple(_anchor(item) for item in cast(tuple[object, ...], value)),
        )
    if type(value) is frozenset:
        return ("frozenset", cast(frozenset[object], value))
    return _anchor(value)


def _root_matches(value: object, expected: object) -> bool:
    if type(value) is tuple:
        if type(expected) is not tuple:
            return False
        expected_parts = cast(tuple[object, ...], expected)
        if len(expected_parts) != 2 or expected_parts[0] != "tuple":
            return False
        children = cast(tuple[object, ...], value)
        anchors = expected_parts[1]
        if type(anchors) is not tuple:
            return False
        typed_anchors = cast(tuple[_FieldAnchor, ...], anchors)
        return len(children) == len(typed_anchors) and all(
            _anchor_matches(child, anchor)
            for child, anchor in zip(children, typed_anchors, strict=True)
        )
    if type(value) is frozenset:
        if type(expected) is not tuple:
            return False
        expected_parts = cast(tuple[object, ...], expected)
        return (
            len(expected_parts) == 2
            and expected_parts[0] == "frozenset"
            and expected_parts[1] is value
        )
    return type(expected) is tuple and _anchor_matches(
        value, cast(_FieldAnchor, expected)
    )


_MAX_INLINE_KEY_NODES = 64


def require_immutable_key(value: object, label: str) -> int:
    """Accept structural immutable keys; reject user-defined mutable hashes."""
    pending: list[tuple[object, bool]] = [(value, False)]
    active: set[int] = set()
    finished: set[int] = set()
    visited = 0
    while pending:
        current, identity, exiting = _pop_visit(pending, active, finished)
        if exiting:
            continue
        if _primitive(current):
            visited += 1
            if visited > _MAX_INLINE_KEY_NODES:
                raise ValueError(
                    f"{label} exceeds the inline descriptor bound; intern it in an arena"
                )
            continue
        if isinstance(current, ArenaHandle):
            current.__post_init__()
            visited += 1
            if visited > _MAX_INLINE_KEY_NODES:
                raise ValueError(
                    f"{label} exceeds the inline descriptor bound; intern it in an arena"
                )
            pending.extend(
                (getattr(current, item.name), False) for item in fields(current)[3:]
            )
            continue
        if identity in active:
            raise ValueError(f"{label} contains a reference cycle")
        if identity in finished:
            continue
        visited += 1
        if visited > _MAX_INLINE_KEY_NODES:
            raise ValueError(
                f"{label} exceeds the inline descriptor bound; intern it in an arena"
            )
        if enter_tuple_node(pending, active, current):
            continue
        if type(current) is frozenset:
            pending.extend((item, False) for item in cast(frozenset[object], current))
            continue
        if is_dataclass(current) and not isinstance(current, type):
            parameters = getattr(type(current), "__dataclass_params__", None)
            if parameters is None or not parameters.frozen:
                raise TypeError(f"{label} must be structurally immutable")
            pending.extend(
                (getattr(current, item.name), False) for item in fields(current)
            )
            continue
        raise TypeError(f"{label} must be a structural immutable key")
    return visited


def typed_payload_equal(left: object, right: object) -> bool:
    """Compare admitted structural keys without Python's bool/int aliases."""
    pending = [(left, right)]
    seen: set[tuple[int, int]] = set()
    while pending:
        first, second = pending.pop()
        if type(first) is not type(second):
            return False
        if _primitive(first):
            if first != second:
                return False
            continue
        pair = id(first), id(second)
        if pair in seen:
            continue
        seen.add(pair)
        if isinstance(first, ArenaHandle):
            assert isinstance(second, ArenaHandle)
            if (
                first.owner is not second.owner
                or first.kind != second.kind
                or first.local_id != second.local_id
            ):
                return False
            pending.extend(
                (getattr(first, item.name), getattr(second, item.name))
                for item in fields(first)[3:]
            )
            continue
        if type(first) is tuple:
            if not extend_typed_tuple_pairs(
                pending, cast(tuple[object, ...], first), second
            ):
                return False
        elif type(first) is frozenset:
            assert isinstance(second, frozenset)
            first_members = cast(frozenset[object], first)
            second_members = cast(frozenset[object], second)
            if {TypedPayloadKey(item) for item in first_members} != {
                TypedPayloadKey(item) for item in second_members
            }:
                return False
        elif is_dataclass(first):
            assert second is not None
            pending.extend(
                (getattr(first, item.name), getattr(second, item.name))
                for item in fields(first)
            )
        else:
            raise TypeError("source image key has an unsupported structural sort")
    return True


def _typed_hash(value: object) -> int:
    """Hash each admitted DAG node once, including shared tuple subgraphs."""
    pending: list[tuple[object, bool]] = [(value, False)]
    hashes: dict[int, int] = {}
    active: set[int] = set()
    while pending:
        current, closing = pending.pop()
        current_value: object = current
        current_kind = type(current_value)
        identity = id(current)
        if identity in hashes:
            continue
        if _primitive(current):
            hashes[identity] = hash((type(current), current))
            continue
        if isinstance(current, ArenaHandle):
            children = tuple(
                cast(object, getattr(current, item.name))
                for item in fields(current)[3:]
            )
            if not children:
                hashes[identity] = hash(
                    (type(current), current.owner, current.kind, current.local_id)
                )
                continue
        elif type(current) is tuple:
            children = cast(tuple[object, ...], current)
        elif current_kind is frozenset:
            children = tuple(cast(frozenset[object], current))
        elif is_dataclass(current):
            children = tuple(
                cast(object, getattr(current, item.name)) for item in fields(current)
            )
        else:
            raise TypeError("source image key has an unsupported structural sort")
        if closing:
            if isinstance(current, ArenaHandle):
                hashes[identity] = hash(
                    (
                        type(current),
                        current.owner,
                        current.kind,
                        current.local_id,
                        tuple(hashes[id(item)] for item in children),
                    )
                )
                active.remove(identity)
                continue
            if current_kind is frozenset:
                parts: object = frozenset(hashes[id(item)] for item in children)
            else:
                parts = tuple(hashes[id(item)] for item in children)
            hashes[identity] = hash((current_kind, parts))
            active.remove(identity)
            continue
        if identity in active:
            raise ValueError("source image typed key contains a reference cycle")
        active.add(identity)
        pending.append((current_value, True))
        pending.extend((child, False) for child in children)
    return hashes[id(value)]


@dataclass(frozen=True, slots=True, eq=False)
class TypedPayloadKey:
    value: Hashable

    def __post_init__(self) -> None:
        require_immutable_key(self.value, "source image typed key")

    def __hash__(self) -> int:
        return _typed_hash(self.value)

    def __eq__(self, other: object) -> bool:
        return type(other) is TypedPayloadKey and typed_payload_equal(
            self.value, other.value
        )


class PublicationSeal(tuple[object, tuple[_Guard, ...], int]):
    """Exact process-local anchors for one immutable publication graph."""

    __slots__ = ()

    def __new__(
        cls, root: object, guards: tuple[_Guard, ...], retained_nodes: int
    ) -> Self:
        # Keep tuple immutability without NamedTuple's mutable class-level
        # defaults dictionary entering every retained execution graph.
        return super().__new__(cls, (root, guards, retained_nodes))

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


class SourceImagePublicationTransaction(Generic[NodeT]):
    """Rollback one provisional source-image node, seal, and index reservation.

    The scheduler supplies its typed stores and index cleanup operation; this
    owner coordinates only the common seal/node/resource and metric lifecycle.
    """

    def __init__(
        self,
        ledger: ResourceLedger,
        nodes: LedgerList[NodeT],
        seals: PublicationSeals,
        node_count_before: int,
        seal_count_before: int,
        reservations: tuple[tuple[int, int, int], ...],
        rollback_indexes: SourceImageIndexRollback,
    ) -> None:
        self._ledger = ledger
        self._nodes = nodes
        self._seals = seals
        self._node_count_before = node_count_before
        self._seal_count_before = seal_count_before
        self._reservations = reservations
        self._rollback_indexes = rollback_indexes
        self._finished = False

    def commit_metrics(self, counters: tuple[str, ...]) -> None:
        if self._finished:
            raise RuntimeError("source image publication is already finished")
        before = {counter: self._ledger.counters.get(counter) for counter in counters}
        try:
            for counter in counters:
                self._ledger.bump(counter)
        except BaseException:
            for counter, value in before.items():
                if value is None:
                    self._ledger.counters.pop(counter, None)
                else:
                    self._ledger.counters[counter] = value
            raise
        self._finished = True

    def rollback(self) -> None:
        if self._finished:
            return
        if len(self._nodes) not in (
            self._node_count_before,
            self._node_count_before + 1,
        ) or len(self._seals.images) not in (
            self._seal_count_before,
            self._seal_count_before + 1,
        ):
            raise RuntimeError("source image rollback found an unexpected suffix")
        self._rollback_indexes()
        if len(self._seals.images) > self._seal_count_before:
            self._seals.pop_image()
        self._nodes.rollback_unpublished(self._node_count_before)
        for owner, entries, nodes in self._reservations:
            self._ledger.release(owner, entries=entries, nodes=nodes)
        self._finished = True


def publication_seal(value: object, ledger: ResourceLedger) -> PublicationSeal:
    """Capture every mutable-via-reflection object once, without hash authority.

    Tuples and frozensets cannot change in place, so the seal retains their identity
    and traverses them only at publication time to find nested dataclasses. Each
    dataclass or arena handle retains an independent shallow field snapshot. Warm
    validation visits guarded objects instead of flattening large primitive tuples.
    """
    root_value: object = value
    root_nodes = 3 + (
        1 + 2 * len(cast(tuple[object, ...], value)) if type(value) is tuple else 0
    )
    retained_nodes = 4 + root_nodes
    ledger.check_capacity(nodes=retained_nodes)
    pending: list[tuple[object, bool]] = [(value, False)]
    active: set[int] = set()
    finished: set[int] = set()
    guards: list[_Guard] = []
    visits = consumed = 0
    try:
        while pending:
            current, identity, leaving = _pop_visit(pending, active, finished)
            if leaving:
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
            if isinstance(current, ArenaHandle) or (
                is_dataclass(current) and not isinstance(current, type)
            ):
                names = tuple(item.name for item in fields(current))
                pinned = tuple(cast(object, getattr(current, name)) for name in names)
                retained_nodes += 5 + 2 * len(names)
                ledger.check_capacity(nodes=retained_nodes)
                guards.append(
                    (
                        current,
                        type(current),
                        names,
                        tuple(
                            item for value in pinned for item in (type(value), value)
                        ),
                    )
                )
                # Arena tokens are identity anchors, never recursively traversed.
                children = (
                    (current.kind, current.local_id, *pinned[3:])
                    if isinstance(current, ArenaHandle)
                    else pinned
                )
            elif type(current) in (tuple, frozenset):
                children = tuple(cast(tuple[object, ...] | frozenset[object], current))
            else:
                raise TypeError("publication contains an unsupported value")
            ledger.check_capacity(nodes=retained_nodes + len(pending) + len(children))
            enter_ordered_children(pending, active, current, children)
            consumed += 8 + 8 * len(children)
        return PublicationSeal(_root_anchor(root_value), tuple(guards), retained_nodes)
    finally:
        ledger.bump(_execution_keys.SOURCE_IMAGE_SEAL_CREATION_VISITS, visits)
        ledger.bump(_execution_keys.SOURCE_IMAGE_SEAL_CREATION_BYTES, consumed)
        # Preserve aggregate counters consumed by existing reporting.
        ledger.bump(_execution_keys.SOURCE_IMAGE_SEAL_VISITS, visits)
        ledger.bump(_execution_keys.SOURCE_IMAGE_SEAL_BYTES, consumed)


def _publication_matches(value: object, seal: PublicationSeal) -> tuple[bool, int]:
    visits = 1
    valid = type(seal) is PublicationSeal and _root_matches(value, seal.root)
    if valid:
        for current, expected_type, names, expected in seal.guards:
            visits += 1
            if type(current) is not expected_type:
                valid = False
                break
            if len(expected) != 2 * len(names) or any(
                not _guard_field_matches(
                    getattr(current, name),
                    cast(type[object], expected[2 * i]),
                    expected[2 * i + 1],
                )
                for i, name in enumerate(names)
            ):
                valid = False
                break
    return valid, visits


def publication_matches(
    value: object, seal: PublicationSeal, ledger: ResourceLedger
) -> bool:
    """Validate exact root and field anchors and charge the runtime visit."""
    valid, visits = _publication_matches(value, seal)
    ledger.bump(_execution_keys.SOURCE_IMAGE_SEAL_VALIDATION_VISITS, visits)
    return valid


def publication_matches_readonly(value: object, seal: PublicationSeal) -> bool:
    """Validate the same independent anchors without changing runtime metrics."""
    return _publication_matches(value, seal)[0]


__all__ = [
    "PublicationSeal",
    "SourceImageIndexRollback",
    "SourceImagePublicationTransaction",
    "TypedPayloadKey",
    "require_immutable_key",
    "typed_payload_equal",
    "publication_matches",
    "publication_matches_readonly",
    "publication_seal",
]


def _pop_visit(
    pending: list[tuple[object, bool]], active: set[int], finished: set[int]
) -> tuple[object, int, bool]:
    """Retire a postorder frame in both key admission and publication sealing."""
    current, leaving = pending.pop()
    identity = id(current)
    if leaving:
        active.remove(identity)
        finished.add(identity)
    return current, identity, leaving
