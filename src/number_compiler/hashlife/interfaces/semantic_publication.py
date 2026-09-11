"""Prepare reduced semantic DAGs for one atomic publication across arenas.

Preparation owns transient nodes only. Its prospective references remain
private until the caller reserves every associated node, interner and parent
binding in one ledger operation. No callback can publish a partial result.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_function_types import (
    SemanticFunctionID,
    SemanticNode,
    SemanticRequest,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)


@dataclass(frozen=True, slots=True)
class _FunctionPublicationJournal:
    node_base: int
    keys: tuple[tuple[SemanticNode, int | None], ...]
    reductions: tuple[tuple[SemanticRequest, SemanticFunctionID | None], ...]


@dataclass(slots=True)
class PreparedFunctions:
    arena: SemanticFunctionArena
    base: int
    nodes: tuple[SemanticNode, ...]
    roots: tuple[SemanticFunctionID, ...]
    reductions: tuple[tuple[SemanticRequest, SemanticFunctionID], ...] = ()
    transaction: _Transaction | None = None
    preparation_entries: int = 0
    preparation_nodes: int = 0
    reserved: bool = False
    converted: tuple[tuple[int, int, int], ...] = ()
    staged_entries: int = 0
    staged_nodes: int = 0

    def validate_current(self) -> None:
        if len(self.arena.nodes) != self.base:
            raise RuntimeError("semantic arena changed during publication preparation")

    def reservations(self) -> tuple[tuple[int, int, int], ...]:
        self.validate_current()
        count = len(self.nodes)
        return (
            (self.arena.node_owner, count, count),
            (self.arena.key_owner, count, 0),
            (self.arena.memo_owner, len(self.reductions), 0),
        )

    def reserve_with(self, additional: tuple[tuple[int, int, int], ...] = ()) -> None:
        """Atomically convert charged construction work into retained ownership."""
        self.validate_current()
        if self.reserved:
            raise RuntimeError("semantic publication was already reserved")
        transaction = self.transaction
        if transaction is None:
            raise RuntimeError("semantic publication lost its construction workspace")
        staged_entries, staged_nodes = transaction.staged_charge
        converted = (*self.reservations(), *additional)
        transaction.reassign_staged(converted)
        self.reserved = True
        self.converted = converted
        self.staged_entries = staged_entries
        self.staged_nodes = staged_nodes

    def cancel(self) -> None:
        """Release all workspace and undo an unpublished ownership conversion."""
        transaction = self.transaction
        if transaction is None:
            return
        if self.reserved:
            transaction.arena.ledger.reassign_many(
                self.converted,
                (
                    (
                        transaction.arena.workspace_owner,
                        self.staged_entries,
                        self.staged_nodes,
                    ),
                ),
            )
            transaction.restore_staged(
                entries=self.staged_entries, nodes=self.staged_nodes
            )
            self.reserved = False
            self.converted = ()
        transaction.close()
        self.transaction = None
        self.nodes = ()
        self.roots = ()
        self.reductions = ()
        self.preparation_entries = 0
        self.preparation_nodes = 0

    def _publish_stores(self) -> _FunctionPublicationJournal:
        self.validate_current()
        if not self.reserved or self.transaction is None:
            raise RuntimeError("semantic publication requires an atomic reservation")
        # Verify both stores before the first mutation, even when an internal
        # caller accidentally supplied only half of the publication credit.
        count = len(self.nodes)
        self.arena.ledger.check_store_capacity(
            self.arena.node_owner, self.base + count, self.base + count
        )
        self.arena.ledger.check_store_capacity(
            self.arena.key_owner, len(self.arena.keys) + count, 0
        )
        self.arena.ledger.check_store_capacity(
            self.arena.memo_owner, len(self.arena.memo) + len(self.reductions), 0
        )
        journal = _FunctionPublicationJournal(
            len(self.arena.nodes),
            tuple((node, self.arena.keys.get(node)) for node in self.nodes),
            tuple(
                (request, self.arena.memo.get(request))
                for request, _result in self.reductions
            ),
        )
        try:
            for offset, node in enumerate(self.nodes):
                self.arena.nodes.append(node)
                self.arena.keys[node] = self.base + offset
            for request, result in self.reductions:
                self.arena.memo[request] = result
        except BaseException:
            self._rollback_stores(journal)
            raise
        return journal

    def _rollback_stores(self, journal: _FunctionPublicationJournal) -> None:
        for request, previous_result in reversed(journal.reductions):
            if previous_result is None:
                if request in self.arena.memo:
                    del self.arena.memo[request]
            else:
                self.arena.memo[request] = previous_result
        for node, previous_identity in reversed(journal.keys):
            if previous_identity is None:
                if node in self.arena.keys:
                    del self.arena.keys[node]
            else:
                self.arena.keys[node] = previous_identity
        self.arena.nodes._rollback_unpublished(journal.node_base)

    def _commit(self) -> None:
        assert self.transaction is not None
        self.arena.ledger.bump(
            "semantic_ite_reduction_publications",
            sum(
                request.operation == "construction-ite"
                for request, _ in self.reductions
            ),
        )
        self.arena.ledger.bump(
            "semantic_bit_admissibility_publications",
            sum(
                request.operation == "bit-admissibility"
                for request, _ in self.reductions
            ),
        )
        self.arena.ledger.bump("semantic_function_published_nodes", len(self.nodes))
        self.transaction.close()
        self.transaction = None
        self.preparation_entries = 0
        self.preparation_nodes = 0
        self.converted = ()
        self.staged_entries = self.staged_nodes = 0

    def publish_reserved(self) -> None:
        journal = self._publish_stores()
        try:
            self._commit()
        except BaseException:
            self._rollback_stores(journal)
            raise


def prepare_functions(
    transaction: _Transaction, roots: tuple[int, ...]
) -> PreparedFunctions:
    """Remap only reachable construction nodes without mutating any arena."""
    arena = transaction.arena
    if len(arena.nodes) != transaction.base:
        raise RuntimeError(
            "semantic transaction was interleaved with another publication"
        )
    staged_count = len(transaction.staged)
    choice_count = len(transaction.choice_requests)
    edge_count = sum(
        len(node.terminal.references) if node.terminal is not None else 2
        for node in transaction.staged
    )
    # At peak, reachability/pending, ordering, remapping, remapped output and
    # the returned immutable node tuple coexist. Reduction candidates and root
    # remaps add the remaining bounded slots. This follows the actual logical
    # containers; it is not a separate semantic size limit.
    preparation_bound = (
        max(
            5 * staged_count,
            staged_count + edge_count + len(roots),
        )
        + len(roots)
        + 2 * min(choice_count, 256)
    )
    preparation_nodes = staged_count
    transaction.reserve_workspace(entries=preparation_bound, nodes=preparation_nodes)
    try:
        reachable: set[int] = set()
        pending = list(roots)
        while pending:
            current = pending.pop()
            if type(current) is not int or not 0 <= current < transaction.base + len(
                transaction.staged
            ):
                raise ValueError("semantic publication root is not a construction node")
            if current < transaction.base or current in reachable:
                continue
            reachable.add(current)
            node = transaction.node(current)
            pending.extend(
                (node.low, node.high)
                if node.terminal is None
                else node.terminal.references
            )
        ordered = sorted(reachable)
        mapped = {old: transaction.base + offset for offset, old in enumerate(ordered)}
        nodes = []
        for old in ordered:
            node = transaction.node(old)
            terminal = node.terminal
            if terminal is not None:
                terminal = SemanticTerminal(
                    terminal.kind,
                    terminal.value,
                    tuple(mapped.get(item, item) for item in terminal.references),
                )
            nodes.append(
                SemanticNode(
                    node.signature,
                    node.variable,
                    mapped.get(node.low, node.low),
                    mapped.get(node.high, node.high),
                    terminal,
                    node.support,
                )
            )
        reductions: list[tuple[SemanticRequest, SemanticFunctionID]] = []
        pending_request = int(
            transaction.request is not None and transaction.request not in arena.memo
        )
        capacity = max(0, 256 - len(arena.memo) - pending_request)
        for arguments in sorted(transaction.choice_requests):
            if len(reductions) >= capacity:
                break
            result = transaction.choices[arguments]
            if result >= transaction.base and result not in mapped:
                continue
            request = SemanticRequest(
                "construction-ite",
                tuple(arena._handle(identity) for identity in arguments),
            )
            if request == transaction.request or request in arena.memo:
                continue
            reductions.append((request, arena._handle(mapped.get(result, result))))
        return PreparedFunctions(
            arena,
            transaction.base,
            tuple(nodes),
            tuple(arena._handle(mapped.get(root, root)) for root in roots),
            tuple(reductions),
            transaction,
            preparation_bound,
            preparation_nodes,
        )
    except BaseException:
        transaction.release_workspace(
            entries=preparation_bound, nodes=preparation_nodes
        )
        raise
