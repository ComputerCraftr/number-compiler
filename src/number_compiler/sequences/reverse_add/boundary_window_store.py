"""Ledger-owned bounded storage for finite reverse boundary relations."""

from __future__ import annotations

from collections import Counter
from collections.abc import Generator, Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Literal, Self

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.resources.stores import LedgerDict, LedgerList

BoundaryOperation = Literal["reverse-add", "double-reverse"]
_RelationKey = tuple[int, BoundaryOperation, int, int, int]


@dataclass(frozen=True, slots=True)
class WindowTile:
    """A fixed-width pair of boundary blocks and cumulative width growth."""

    prefix: int
    suffix: int
    growth: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int or value < 0
            for value in (self.prefix, self.suffix, self.growth)
        ):
            raise ValueError("boundary tile fields must be nonnegative exact integers")


@dataclass(frozen=True, slots=True)
class BoundaryRelationRecord:
    """Exact relation outcomes stored behind one validated owner boundary."""

    outcomes: frozenset[WindowTile]


class WindowRelationBudgetExceeded(ValueError):
    """A finite boundary relation was not completed within its work limits."""


class BoundaryRelationStore:
    """Term-owned relation memo with explicit entry and state limits."""

    def __init__(
        self,
        ledger: ResourceLedger,
        *,
        max_entries: int,
        max_states: int,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("boundary relation store requires a resource ledger")
        self.ledger = ledger
        self.max_entries = require_integer(max_entries, "boundary entry limit", 1)
        self.max_states = require_integer(max_states, "boundary state limit", 1)
        owner = ledger.register(
            f"reverse-boundary-window-{ledger.owner_count}",
            "reverse_boundary_window_relation",
        )
        self.memo: LedgerDict[_RelationKey, BoundaryRelationRecord] = ledger.make_dict(
            owner, nodes_per_entry=2, write_once=True
        )
        self.retained_states = 0
        self._state_owner = ledger.register(
            f"reverse-boundary-states-{ledger.owner_count}",
            "reverse_boundary_window_states",
        )
        self._state_tiles: LedgerList[WindowTile] = ledger.make_list(
            self._state_owner, nodes_per_entry=1
        )
        self._workspace_owner = ledger.register(
            f"reverse-boundary-workspace-{ledger.owner_count}",
            "reverse_boundary_window_workspace",
        )
        self._worklist: LedgerList[tuple[_RelationKey, bool]] = ledger.make_list(
            self._workspace_owner, nodes_per_entry=1, append_only=False
        )

    @property
    def worklist(self) -> LedgerList[tuple[_RelationKey, bool]]:
        return self._worklist

    @contextmanager
    def charged_frontier(self) -> Generator[_LedgerFrontier, None, None]:
        """Expose the single-owner, ledger-accounted temporal worklist."""
        if self._worklist:
            raise RuntimeError("boundary relation worklist is already active")
        frontier = _LedgerFrontier(self)
        try:
            yield frontier
        finally:
            frontier.clear()

    def transient_states(self) -> _TransientBoundaryStates:
        return _TransientBoundaryStates(self)

    def publish(self, key: _RelationKey, value: frozenset[WindowTile]) -> bool:
        if key in self.memo:
            return False
        if any(tile.growth.bit_length() > 64 for tile in value):
            raise WindowRelationBudgetExceeded(
                "boundary growth exceeds the bounded occurrence representation"
            )
        if len(self.memo) >= self.max_entries:
            raise WindowRelationBudgetExceeded("boundary relation entry limit exceeded")
        if self.retained_states + len(value) > self.max_states:
            raise WindowRelationBudgetExceeded("boundary retained-state limit exceeded")
        record = BoundaryRelationRecord(value)
        reservation = (
            (self.memo.owner, 1, self.memo.nodes_per_entry),
            (self._state_owner, len(value), len(value)),
        )
        self.ledger.reserve_many(reservation)
        state_count = len(self._state_tiles)
        try:
            self.memo[key] = record
            for tile in value:
                self._state_tiles.append(tile)
        except BaseException:
            self._state_tiles.rollback_unpublished(state_count)
            if self.memo.get(key) is record:
                self.memo.rollback_unpublished(key, record)
            else:
                self.ledger.release(
                    self.memo.owner, entries=1, nodes=self.memo.nodes_per_entry
                )
            self.ledger.release(self._state_owner, entries=len(value), nodes=len(value))
            raise
        self.retained_states += len(value)
        return True


class _LedgerFrontier:
    """Stack view that charges every transient frame before insertion."""

    __slots__ = ("_store",)

    def __init__(self, store: BoundaryRelationStore) -> None:
        self._store = store

    def __bool__(self) -> bool:
        return bool(self._store._worklist)

    def push(self, frame: tuple[_RelationKey, bool]) -> None:
        ledger = self._store.ledger
        owner = self._store._workspace_owner
        prior_size = len(self._store._worklist)
        ledger.reserve(owner, entries=1, nodes=1)
        try:
            self._store._worklist.append(frame)
        except BaseException:
            try:
                if len(self._store._worklist) > prior_size:
                    self._store._worklist.rollback_unpublished(prior_size)
            finally:
                ledger.release(owner, entries=1, nodes=1)
            raise

    def extend(self, frames: Iterator[tuple[_RelationKey, bool]]) -> None:
        for frame in frames:
            self.push(frame)

    def pop(self) -> tuple[_RelationKey, bool]:
        frame = self._store._worklist.pop()
        self._store.ledger.release(self._store._workspace_owner, entries=1, nodes=1)
        return frame

    def clear(self) -> None:
        pending = len(self._store._worklist)
        if not pending:
            return
        self._store._worklist.clear()
        self._store.ledger.release(
            self._store._workspace_owner, entries=pending, nodes=pending
        )


class _TransientBoundaryStates:
    """Set builder charging one live node for each distinct temporary state."""

    __slots__ = ("_reserved", "_store", "_values")

    def __init__(self, store: BoundaryRelationStore) -> None:
        self._store = store
        self._values: set[WindowTile] = set()
        self._reserved = 0

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        if self._reserved:
            self._store.ledger.release(
                self._store._workspace_owner, nodes=self._reserved
            )
            self._reserved = 0

    def add(self, tile: WindowTile) -> None:
        if tile in self._values:
            return
        owner = self._store._workspace_owner
        self._store.ledger.reserve(owner, nodes=1)
        try:
            self._values.add(tile)
        except BaseException:
            self._store.ledger.release(owner, nodes=1)
            raise
        self._reserved += 1

    def __iter__(self) -> Iterator[WindowTile]:
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)

    def freeze(self) -> frozenset[WindowTile]:
        return frozenset(self._values)


def audit_reverse_boundary_window_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate retained window relations against their exact ledger owner."""
    from number_compiler.sequences.reverse_add.boundary_window import (
        BoundaryObservationCacheRecord,
        ReverseBoundaryWindowObservation,
        ReverseBoundaryWindowObserver,
        _observation_fields,
    )

    if (
        type(ledger) is not ResourceLedger
        or type(root) is not ReverseBoundaryWindowObserver
    ):
        return PayloadAuditContribution()
    memo = root._relations.memo
    owner = memo.owner
    try:
        root._validate_authority()
        inventory = ledger.inventory_owner(owner)
        workspace = ledger.inventory_owner(root._relations._workspace_owner)
        state_owner = root._relations._state_owner
        state_inventory = ledger.inventory_owner(state_owner)
        observation_memo = root._observation_memo
        observation_owner = observation_memo.owner
        observation_inventory = ledger.inventory_owner(observation_owner)
        worklist = root._relations.worklist
        if (
            inventory.role != "reverse_boundary_window_relation"
            or inventory.entries != len(memo)
            or inventory.nodes != len(memo) * memo.nodes_per_entry
            or workspace.role != "reverse_boundary_window_workspace"
            or workspace.entries != len(worklist)
            or workspace.nodes != len(worklist)
            or state_inventory.role != "reverse_boundary_window_states"
            or state_inventory.entries != root._relations.retained_states
            or state_inventory.nodes != root._relations.retained_states
            or len(root._relations._state_tiles) != root._relations.retained_states
            or ledger.registered_container(root._relations._workspace_owner)
            is not worklist
            or worklist
            or observation_inventory.role != "reverse_boundary_window_observation"
            or observation_inventory.entries != len(observation_memo)
            or observation_inventory.nodes != len(observation_memo) * 16
            or len(observation_memo) > 1
            or ledger.registered_container(observation_owner)
            is not root._observation_data
        ):
            raise ValueError("boundary relation inventory is not exact")
        retained_states = 0
        expected_nodes = len(memo) * memo.nodes_per_entry
        expected_state_tiles: Counter[WindowTile] = Counter()
        approved: list[PayloadAuditEntry] = []
        for key, record in memo.items():
            if (
                type(key) is not tuple
                or len(key) != 5
                or type(key[0]) is not int
                or key[0] not in (2, 4, 8)
                or key[1] != "reverse-add"
                or any(type(item) is not int for item in key[2:])
                or key[4] < 0
                or not 10 ** (key[0] - 1) <= key[2] < 10 ** key[0]
                or not 0 <= key[3] < 10 ** key[0]
                or type(record) is not BoundaryRelationRecord
                or type(record.outcomes) is not frozenset
                or len(record.outcomes) > root.max_states
            ):
                raise ValueError("malformed boundary relation key or result")
            span = 1 << key[4]
            for tile in record.outcomes:
                if (
                    type(tile) is not WindowTile
                    or type(tile.prefix) is not int
                    or type(tile.suffix) is not int
                    or type(tile.growth) is not int
                    or not 10 ** (key[0] - 1) <= tile.prefix < 10 ** key[0]
                    or not 0 <= tile.suffix < 10 ** key[0]
                    or not 0 <= tile.growth <= span
                    or tile.growth.bit_length() > 64
                ):
                    raise ValueError("malformed boundary relation outcome")
            retained_states += len(record.outcomes)
            expected_state_tiles.update(record.outcomes)
            approved.extend(PayloadAuditEntry(owner, item) for item in (key, record))
        actual_state_tiles = Counter(root._relations._state_tiles)
        if (
            retained_states != root._relations.retained_states
            or retained_states > root.max_relation_states
            or expected_nodes != inventory.nodes
            or len(memo) > root.max_relation_entries
            or actual_state_tiles != expected_state_tiles
        ):
            raise ValueError("boundary relation state accounting mismatch")
        approved.extend(
            PayloadAuditEntry(state_owner, tile)
            for tile in root._relations._state_tiles
        )
        cached = root._cached_record()
        if cached is not None:
            if (
                type(cached) is not BoundaryObservationCacheRecord
                or type(cached.observation) is not ReverseBoundaryWindowObservation
                or type(cached.fields) is not tuple
                or _observation_fields(cached.observation) != cached.fields
            ):
                raise ValueError("boundary observation cache is stale")
            cached.observation.__post_init__()
        approved.extend(
            PayloadAuditEntry(observation_owner, item)
            for key, value in observation_memo.items()
            for item in (key, value)
        )
        return PayloadAuditContribution(tuple(approved), ())
    except (AttributeError, IndexError, KeyError, TypeError, ValueError):
        return PayloadAuditContribution(invalid=(PayloadAuditEntry(owner, root),))


__all__ = [
    "BoundaryOperation",
    "BoundaryRelationRecord",
    "BoundaryRelationStore",
    "WindowRelationBudgetExceeded",
    "WindowTile",
    "_RelationKey",
    "audit_reverse_boundary_window_owner",
]
