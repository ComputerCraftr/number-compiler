"""Resource-ledger-backed interning for the shared SLP grammar owner."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping, MutableMapping, Sequence
from dataclasses import dataclass
from typing import TypeVar, cast

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.slp import SLPArena, SLPMetrics, SLPNode
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, clear_accounted_store
from number_compiler.resources.stores import LedgerList

_Key = TypeVar("_Key")


@dataclass(frozen=True, slots=True)
class LedgerSLPArenaAuditSnapshot:
    """Detached typed state used to audit one ledger-owned SLP arena."""

    ledger: ResourceLedger
    owners: object
    empty_id: object
    closed: object
    cleanup_complete: object
    nodes_released: object
    node_store: LedgerList[SLPNode]
    node_store_identity: int
    node_store_alias_matches: bool
    node_rows: tuple[object, ...]
    term_memo: OwnedMemo[int, int]
    term_store_identity: int
    term_alias_matches: bool
    term_rows: tuple[tuple[object, object], ...]
    concat_memo: OwnedMemo[tuple[int, int], int]
    concat_store_identity: int
    concat_alias_matches: bool
    concat_rows: tuple[tuple[object, object], ...]
    repeat_memo: OwnedMemo[tuple[int, int], int]
    repeat_store_identity: int
    repeat_alias_matches: bool
    repeat_rows: tuple[tuple[object, object], ...]


class LedgerSLPArena(SLPArena):
    """The common hash-consed SLP arena with ledger-owned storage.

    Family owners provide a short accounting role prefix; grammar semantics
    and node canonicalization remain those of :class:`SLPArena`.
    """

    __slots__ = (
        "__weakref__",
        "_cat_store",
        "_cleanup_complete",
        "_closed",
        "_nodes_released",
        "_nodes_pending_clear_entries",
        "_nodes_pending_clear_nodes",
        "_nodes_store",
        "_rep_store",
        "_term_store",
        "ledger",
        "owners",
    )

    def __init__(self, ledger: ResourceLedger, prefix: str, owner_kind: str) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("ledgered SLP arena requires a resource ledger")
        if type(prefix) is not str or not prefix:
            raise ValueError("ledgered SLP arena requires a nonempty owner prefix")
        if type(owner_kind) is not str or not owner_kind:
            raise ValueError("ledgered SLP arena requires a nonempty owner kind")
        self._closed = False
        self._cleanup_complete = False
        self._nodes_released = False
        self._nodes_pending_clear_entries = 0
        self._nodes_pending_clear_nodes = 0
        self._node_id_generation = 0
        self._node_storage_poisoned = False
        self.ledger = ledger
        self.owners = (
            ledger.register(prefix + "-slp-nodes", owner_kind + "_grammar"),
            ledger.register(prefix + "-slp-terminals", owner_kind + "_interner"),
            ledger.register(prefix + "-slp-concats", owner_kind + "_interner"),
            ledger.register(prefix + "-slp-repeats", owner_kind + "_interner"),
        )
        self._nodes_store: LedgerList[SLPNode] = ledger.make_list(
            self.owners[0], nodes_per_entry=1
        )
        self.nodes = self._nodes_store
        self._term_store: OwnedMemo[int, int] = OwnedMemo(ledger, self.owners[1])
        self._cat_store: OwnedMemo[tuple[int, int], int] = OwnedMemo(
            ledger, self.owners[2]
        )
        self._rep_store: OwnedMemo[tuple[int, int], int] = OwnedMemo(
            ledger, self.owners[3]
        )
        self._term = self._term_store
        self._cat = self._cat_store
        self._rep = self._rep_store
        try:
            self.empty_id = self._add("EMPTY", 0)
            ledger.register_execution_root(self)
        except BaseException as error:
            try:
                self.dispose()
            except BaseException as cleanup_error:
                raise error from cleanup_error
            raise

    @property
    def audit_interner_stores(
        self,
    ) -> tuple[
        Mapping[int, object],
        Mapping[tuple[int, int], object],
        Mapping[tuple[int, int], object],
    ]:
        """Return the exact registered SLP interners for read-only auditing."""
        self._check_open()
        return (
            self._term_store.audit_container,
            self._cat_store.audit_container,
            self._rep_store.audit_container,
        )

    def existing_concat(self, left: int, right: int) -> int | None:
        return self._cat.get((left, right))

    def existing_repeat_entry(self, key: tuple[int, int]) -> int | None:
        return self._rep.get(key)

    def existing_terminal(self, symbol: int) -> int | None:
        """Read an existing terminal without interning or charging a node."""
        return self._term.get(symbol)

    def audit_snapshot(self) -> LedgerSLPArenaAuditSnapshot:
        """Capture exact stores, lifecycle state, and detached retained rows."""
        from number_compiler.resources.payload_containers import audit_mapping_items

        return LedgerSLPArenaAuditSnapshot(
            ledger=self.ledger,
            owners=cast(object, self.owners),
            empty_id=cast(object, self.empty_id),
            closed=cast(object, self._closed),
            cleanup_complete=cast(object, self._cleanup_complete),
            nodes_released=cast(object, self._nodes_released),
            node_store=self._nodes_store,
            node_store_identity=id(self._nodes_store),
            node_store_alias_matches=self.nodes is self._nodes_store,
            node_rows=tuple(
                cast(object, value) for value in self._nodes_store.snapshot()
            ),
            term_memo=self._term_store,
            term_store_identity=id(self._term_store.audit_snapshot().container),
            term_alias_matches=self._term is self._term_store,
            term_rows=tuple(
                (cast(object, key), cast(object, value))
                for key, value in audit_mapping_items(self._term_store)
            ),
            concat_memo=self._cat_store,
            concat_store_identity=id(self._cat_store.audit_snapshot().container),
            concat_alias_matches=self._cat is self._cat_store,
            concat_rows=tuple(
                (cast(object, key), cast(object, value))
                for key, value in audit_mapping_items(self._cat_store)
            ),
            repeat_memo=self._rep_store,
            repeat_store_identity=id(self._rep_store.audit_snapshot().container),
            repeat_alias_matches=self._rep is self._rep_store,
            repeat_rows=tuple(
                (cast(object, key), cast(object, value))
                for key, value in audit_mapping_items(self._rep_store)
            ),
        )

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed ledgered SLP arena")

    def empty(self) -> int:
        self._check_open()
        return self.empty_id

    def terminal(self, symbol: int) -> int:
        self._check_open()
        return super().terminal(symbol)

    def concat(self, left: int, right: int) -> int:
        self._check_open()
        return super().concat(left, right)

    def repeat(self, child: int, count: int) -> int:
        self._check_open()
        return super().repeat(child, count)

    def concat_many(self, nodes: Iterable[int]) -> int:
        self._check_open()
        return super().concat_many(nodes)

    def word(self, word: Sequence[int]) -> int:
        self._check_open()
        return super().word(word)

    def materialize(self, root: int) -> tuple[int, ...]:
        self._check_open()
        return super().materialize(root)

    def reachable(self, root: int) -> set[int]:
        self._check_open()
        return super().reachable(root)

    def metrics(self, root: int) -> SLPMetrics:
        self._check_open()
        return super().metrics(root)

    def _add(self, kind: str, length: int, **fields: int) -> int:
        self._check_open()
        node_id = len(self.nodes)
        owner = self.owners[0]
        self.ledger.reserve(owner, entries=1, nodes=1)
        try:
            self.nodes.append(SLPNode(node_id, kind, int(length), **fields))
        except BaseException:
            self._rollback_failed_node_publication(node_id)
            raise
        record_slp_metrics(nodes=1)
        return node_id

    def _rollback_failed_node_publication(self, node_id: int) -> None:
        """Undo one reserved append and release exactly the removed row charge."""
        before = len(self.nodes)
        if before <= node_id:
            self._record_pending_node_clear(
                self._nodes_pending_clear_entries + 1,
                self._nodes_pending_clear_nodes + 1,
            )
            self._rollback_node_store_to(before, invalidate_generation=False)
            return

        self._rollback_node_store_to(node_id)

    def _record_pending_node_clear(self, entries: int, nodes: int) -> None:
        self._nodes_pending_clear_entries = entries
        self._nodes_pending_clear_nodes = nodes

    def _rollback_node_store_to(
        self,
        size: int,
        *,
        invalidate_generation: bool = True,
    ) -> None:
        """Rollback a node suffix and reconcile its exact ledger delta on failure."""
        if size == len(self.nodes) and not (
            self._nodes_pending_clear_entries or self._nodes_pending_clear_nodes
        ):
            return
        if invalidate_generation and size < len(self.nodes):
            self._invalidate_node_ids()
        clear_accounted_store(
            self.ledger,
            self.owners[0],
            lambda: self._nodes_store.rollback_unpublished(size),
            lambda: (len(self.nodes), len(self.nodes)),
            (
                self._nodes_pending_clear_entries,
                self._nodes_pending_clear_nodes,
            ),
            self._record_pending_node_clear,
        )

    def _add_interned(
        self,
        kind: str,
        length: int,
        table: MutableMapping[_Key, int],
        key: _Key,
        **fields: int,
    ) -> int:
        self._check_open()
        owner = self.owners[0]
        self.ledger.reserve(owner, entries=1, nodes=1)
        node_id = len(self.nodes)
        try:
            self.nodes.append(SLPNode(node_id, kind, int(length), **fields))
            table[key] = node_id
        except BaseException as error:
            try:
                published_id = table.get(key)
            except BaseException as cleanup_error:
                # Keep the node if publication state cannot be observed. An
                # orphaned node is safe; rolling it back could leave a cache
                # key that aliases a future node ID.
                fields.clear()
                raise error from cleanup_error
            if (
                len(self.nodes) > node_id
                and type(published_id) is int
                and published_id == node_id
            ):
                # A store cleanup failure may leave the exact key in place.
                # Retain its node so the interner never names a recycled ID.
                fields.clear()
                raise
            try:
                self._rollback_failed_node_publication(node_id)
            except BaseException as cleanup_error:
                fields.clear()
                raise error from cleanup_error
            fields.clear()
            raise
        record_slp_metrics(nodes=1)
        return node_id

    def rollback_unpublished_suffix(
        self,
        first_new_node: int,
        *,
        before_remove: Callable[[int], None] | None = None,
    ) -> None:
        """Remove an unpublished suffix and its exact interner publications."""
        self._check_open()
        # A prior callback may have removed rows but failed during ledger
        # reconciliation. Settle that delta before validating a retry boundary.
        if self._nodes_pending_clear_entries or self._nodes_pending_clear_nodes:
            self._rollback_node_store_to(len(self.nodes), invalidate_generation=False)
        if type(first_new_node) is not int or not 1 <= first_new_node <= len(
            self.nodes
        ):
            raise ValueError("invalid SLP rollback boundary")
        if len(self.nodes) > first_new_node:
            # Invalidate before callbacks/removals so even a partial rollback
            # cannot leave node-ID keyed consumers using the old generation.
            self._invalidate_node_ids()
        while len(self.nodes) > first_new_node:
            node_id = len(self.nodes) - 1
            node = self.nodes[node_id]
            if before_remove is not None:
                before_remove(node_id)
            if node.kind == "TERM":
                if (
                    type(node.symbol) is int
                    and self._term_store.get(node.symbol) == node_id
                ):
                    del self._term_store[node.symbol]
            elif node.kind == "CONCAT":
                if type(node.left) is int and type(node.right) is int:
                    key = node.left, node.right
                    if self._cat_store.get(key) == node_id:
                        del self._cat_store[key]
            elif node.kind == "REPEAT":
                if type(node.child) is int and type(node.count) is int:
                    key = node.child, node.count
                    if self._rep_store.get(key) == node_id:
                        del self._rep_store[key]
            else:
                raise AssertionError("cannot roll back the SLP empty node")
            self._rollback_node_store_to(node_id, invalidate_generation=False)

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._invalidate_node_ids()
        self._closed = True

        def release_nodes() -> None:
            self._rollback_node_store_to(0, invalidate_generation=False)
            if not len(self.nodes) and not self._nodes_released:
                self.ledger.mark_disposed(self.owners[0])
                self._nodes_released = True

        cleanup_all(
            (
                self._rep_store.dispose,
                self._cat_store.dispose,
                self._term_store.dispose,
                release_nodes,
            )
        )
        self._cleanup_complete = True
