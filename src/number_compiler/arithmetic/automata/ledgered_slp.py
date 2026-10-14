"""Resource-ledger-backed interning for the shared SLP grammar owner."""

from __future__ import annotations

from collections.abc import Iterable, MutableMapping, Sequence
from typing import TypeVar

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.slp import SLPArena, SLPMetrics, SLPNode
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.stores import LedgerList

_Key = TypeVar("_Key")


class LedgerSLPArena(SLPArena):
    """The common hash-consed SLP arena with ledger-owned storage.

    Family owners provide a short accounting role prefix; grammar semantics
    and node canonicalization remain those of :class:`SLPArena`.
    """

    __slots__ = (
        "__weakref__",
        "_cleanup_complete",
        "_closed",
        "_nodes_released",
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
        self.ledger = ledger
        self.owners = (
            ledger.register(prefix + "-slp-nodes", owner_kind + "_grammar"),
            ledger.register(prefix + "-slp-terminals", owner_kind + "_interner"),
            ledger.register(prefix + "-slp-concats", owner_kind + "_interner"),
            ledger.register(prefix + "-slp-repeats", owner_kind + "_interner"),
        )
        self.nodes: LedgerList[SLPNode] = ledger.make_list(
            self.owners[0], nodes_per_entry=1
        )
        self._term: OwnedMemo[int, int] = OwnedMemo(ledger, self.owners[1])
        self._cat: OwnedMemo[tuple[int, int], int] = OwnedMemo(ledger, self.owners[2])
        self._rep: OwnedMemo[tuple[int, int], int] = OwnedMemo(ledger, self.owners[3])
        try:
            self.empty_id = self._add("EMPTY", 0)
            ledger.register_execution_root(self)
        except BaseException as error:
            try:
                self.dispose()
            except BaseException as cleanup_error:
                raise error from cleanup_error
            raise

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
            if len(self.nodes) > node_id:
                self.nodes._rollback_unpublished(node_id)
            self.ledger.release(owner, entries=1, nodes=1)
            raise
        record_slp_metrics(nodes=1)
        return node_id

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
        except BaseException:
            if len(self.nodes) > node_id:
                self.nodes._rollback_unpublished(node_id)
            self.ledger.release(owner, entries=1, nodes=1)
            raise
        record_slp_metrics(nodes=1)
        return node_id

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        count = len(self.nodes)

        def release_nodes() -> None:
            self.nodes._rollback_unpublished(0)
            if not len(self.nodes) and not self._nodes_released:
                self.ledger.release(self.owners[0], entries=count, nodes=count)
                self._nodes_released = True
            if not len(self.nodes):
                self.ledger.mark_disposed(self.owners[0])

        cleanup_all(
            (
                self._rep.dispose,
                self._cat.dispose,
                self._term.dispose,
                release_nodes,
            )
        )
        self._cleanup_complete = True
