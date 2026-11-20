"""Preflighted reference-count plans for persistent immutable DAG roots."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, Protocol, Self, TypeVar

from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.owned_memo import LedgerReservation

_Node = TypeVar("_Node")


class _RootLeaseOwner(Protocol[_Node]):
    def action(self, root: _Node) -> object: ...

    def release_temporary_root(self, root: _Node) -> None: ...

    def forget_temporary_root_lease(self, lease: TemporaryRootLease[_Node]) -> None: ...

    def fail_closed(self) -> None: ...

    def dispose(self) -> None: ...


class TemporaryRootLease(Generic[_Node]):
    """Scoped pin for one root during an atomic persistent-DAG replacement."""

    __slots__ = ("_owner", "_root", "_active", "_committed")

    def __init__(self, owner: _RootLeaseOwner[_Node], root: _Node) -> None:
        self._owner = owner
        self._root = root
        self._active = False
        self._committed = False

    @property
    def root(self) -> _Node:
        """Return the pinned root without allowing reassignment through the API."""
        return self._root

    def __enter__(self) -> Self:
        if not self._active:
            raise RuntimeError("temporary root lease is not active")
        return self

    def activate(self) -> None:
        if self._active:
            raise RuntimeError("temporary root lease is already active")
        self._active = True

    def commit(self) -> None:
        if not self._active:
            raise RuntimeError("temporary root lease is not active")
        self._committed = True

    def close(self, *, restore: bool) -> None:
        if not self._active:
            return
        owner = self._owner
        try:
            if restore or not self._committed:
                owner.action(self.root)
            owner.release_temporary_root(self.root)
            owner.forget_temporary_root_lease(self)
        except BaseException:
            self._active = False
            cleanup_all((owner.fail_closed, owner.dispose))
            raise
        self._active = False

    def __exit__(self, exc_type: object, _exc: object, _traceback: object) -> None:
        self.close(restore=exc_type is not None)

    def revoke(self) -> None:
        self._active = False


@dataclass(frozen=True, slots=True)
class ReferenceDelta(Generic[_Node]):
    """One exact node's incoming-edge count before and after a root switch."""

    key: int
    node: _Node
    before: int
    after: int


@dataclass(frozen=True, slots=True)
class AtomicRootDeltaPlan(Generic[_Node]):
    """Charged plan for replacing one pinned DAG root with another.

    The plan records strong node references as well as their ``id`` keys, so
    identities cannot be recycled between preparation and commit. A node's
    outgoing edges enter the plan only if its planned incoming count reaches
    zero. The caller remains responsible for the associated action rows,
    rollback journal, and delayed publication of its root pointer.
    """

    changes: tuple[ReferenceDelta[_Node], ...]
    reserved_nodes: int
    reserved_entries: int
    visited_nodes: int
    visited_edges: int

    def validate_current(
        self,
        lookup: Callable[[int], tuple[_Node, int] | None],
    ) -> None:
        """Reject a stale plan if any reference row changed before commit."""
        for change in self.changes:
            current = lookup(change.key)
            if change.before == 0:
                if current is not None:
                    raise RuntimeError("root delta plan found a new reference row")
            elif (
                current is None
                or current[0] is not change.node
                or current[1] != change.before
            ):
                raise RuntimeError("root delta plan found a changed reference row")


def plan_root_reference_changes(
    added_roots: tuple[_Node, ...],
    removed_roots: tuple[_Node, ...],
    *,
    lookup: Callable[[int], tuple[_Node, int] | None],
    children: Callable[[_Node], tuple[_Node, ...]],
    reservation: LedgerReservation,
) -> AtomicRootDeltaPlan[_Node]:
    """Plan an atomic batch of positive and negative root pins.

    All additions are simulated before removals so an added root protects any
    shared descendants from a same-transaction release. Each tuple entry is a
    distinct root pin; the planner groups repeated roots in its staged deltas.

    Scratch capacity is reserved before each plan row and pending edge is
    allocated. Repeated child references are combined into one counted
    decrement, while every original incoming edge remains represented. Pending
    edge charges are released as they are consumed; the
    returned ``reserved_nodes`` covers the persistent delta records. The
    caller must transfer that charge to an owner that remains live through
    commit/rollback before closing the reservation.

    The lookup callback returns the exact live node and its incoming-reference
    count. Missing nodes are admitted only for the positive new-root pin. A
    node's outgoing edges are expanded only when its simulated count transitions
    to zero; repeated edges to one child are merged into one counted delta.
    """
    if (
        type(reservation) is not LedgerReservation
        or type(added_roots) is not tuple
        or type(removed_roots) is not tuple
    ):
        raise TypeError("root delta planning requires an exact ledger reservation")

    # The plan dictionary keeps each exact node alive beside its id key and
    # stores (original_count, simulated_count). Entry capacity for a new root
    # is checked before any retained mapping insertion can occur.
    staged: dict[int, tuple[_Node, int, int]] = {}
    pending: list[tuple[_Node, int]] = []
    persistent_nodes = 0
    transient_edges = 0
    reserved_entries = 0
    visited_nodes = 0
    visited_edges = 0

    def queue_release(node: _Node, references: int) -> None:
        nonlocal transient_edges, visited_edges
        reservation.reserve(nodes=12)
        try:
            pending.append((node, -references))
        except BaseException:
            reservation.release(nodes=12)
            raise
        transient_edges += 12
        visited_edges += references

    def stage(node: _Node, delta: int) -> None:
        nonlocal persistent_nodes, reserved_entries
        nonlocal visited_nodes
        if type(delta) is not int or delta == 0 or delta > 1:
            raise ValueError("root reference deltas must be positive pins or releases")
        key = id(node)
        previous = staged.get(key)
        if previous is None:
            reservation.reserve(nodes=32)
            persistent_nodes += 32
            current = lookup(key)
            if current is not None and current[0] is not node:
                raise RuntimeError("reference identity was recycled while planning")
            before = 0 if current is None else current[1]
            if current is None and delta < 0:
                raise RuntimeError("root reference plan releases a missing row")
            if current is None and delta > 0:
                reservation.reserve(entries=1, nodes=4)
                reserved_entries += 1
            if current is not None and (type(before) is not int or before < 1):
                raise RuntimeError("reference count is malformed")
            prior = before
        else:
            if previous[0] is not node:
                raise RuntimeError("reference identity was recycled in the plan")
            before, prior = previous[1], previous[2]
        after = prior + delta
        if after < 0:
            raise RuntimeError("root reference plan releases an unowned edge")
        if before == 0 and after == 0:
            # A same-plan add/remove of a previously missing root has no
            # committed row and therefore must not release nonexistent child
            # references.
            staged.pop(key, None)
            persistent_nodes -= 32
            reservation.release(nodes=32)
            if reserved_entries:
                reserved_entries -= 1
                reservation.release(entries=1, nodes=4)
            visited_nodes += 1
            return
        staged[key] = node, before, after
        visited_nodes += 1
        if after == 0 and prior > 0 and before > 0:
            outgoing = children(node)
            if type(outgoing) is not tuple:
                raise TypeError("reference graph children must be an immutable tuple")
            group_scratch = 16 * len(outgoing)
            if group_scratch:
                reservation.reserve(nodes=group_scratch)
            try:
                grouped: dict[int, tuple[_Node, int]] = {}
                for child in outgoing:
                    child_key = id(child)
                    prior_child = grouped.get(child_key)
                    if prior_child is not None:
                        if prior_child[0] is not child:
                            raise RuntimeError("recycled identity in child edge list")
                        grouped[child_key] = child, prior_child[1] + 1
                    else:
                        grouped[child_key] = child, 1
                for child, references in grouped.values():
                    queue_release(child, references)
            finally:
                if group_scratch:
                    reservation.release(nodes=group_scratch)

    try:
        for root in added_roots:
            stage(root, 1)
        for root in removed_roots:
            queue_release(root, 1)
        while pending:
            node, delta = pending.pop()
            reservation.release(nodes=12)
            transient_edges -= 12
            stage(node, delta)
        if transient_edges != 0:
            raise RuntimeError("root delta planner retained edge scratch")
        changes = tuple(
            ReferenceDelta(key, node, before, after)
            for key, (node, before, after) in staged.items()
        )
        return AtomicRootDeltaPlan(
            changes,
            persistent_nodes,
            reserved_entries,
            visited_nodes,
            visited_edges,
        )
    finally:
        pending.clear()
        staged.clear()


__all__ = [
    "AtomicRootDeltaPlan",
    "ReferenceDelta",
    "plan_root_reference_changes",
]
