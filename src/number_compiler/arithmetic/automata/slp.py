"""Balanced SLP metadata and exact regular-transduction projection.

Hash-consed grammars preserve repeated words without expanding their copies.
DFA actions use binary powers; finite paired-context orbits retain repeated
emissions as SLP nodes rather than visiting every represented symbol.
"""

from __future__ import annotations

from collections.abc import Iterable, MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass
from math import lcm
from typing import TYPE_CHECKING, Never, SupportsIndex, TypeVar, cast

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.slp_cache_audit import (
    SLPCacheAuditView,
    slp_cache_audit_view,
)
from number_compiler.arithmetic.automata.slp_node_storage import SLPNodeStorage
from number_compiler.arithmetic.automata.transducer import (
    transduction_midpoints,
)
from number_compiler.arithmetic.contracts.iterative_queries import push_binary_children
from number_compiler.arithmetic.fields.radix import bit_width

if TYPE_CHECKING:
    from number_compiler.arithmetic.automata.transducer import BimachineProtocol
    from number_compiler.resources.owned_memo import OwnedMemo

_bits = bit_width
_InternKey = TypeVar("_InternKey")
_CacheKey = TypeVar("_CacheKey")


@dataclass(frozen=True, slots=True)
class SLPNode:
    id: int
    kind: str
    length: int
    symbol: int = -1
    left: int = -1
    right: int = -1
    child: int = -1
    count: int = 0


def canonical_repeat_key(
    nodes: Sequence[SLPNode], empty_id: int, child: int, count: int
) -> int | tuple[int, int]:
    """Normalize identity cases and nested repeats without allocating nodes."""
    if count < 0:
        raise ValueError(count)
    if count == 0 or child == empty_id:
        return empty_id
    if count == 1:
        return child
    node = nodes[child]
    while node.kind == "REPEAT":
        count *= node.count
        child = node.child
        node = nodes[child]
    return child, count


@dataclass(frozen=True, slots=True)
class SLPMetrics:
    word_length: int
    reachable_nodes: int
    terminals: int
    concats: int
    repeats: int
    depth: int
    description_bits: int


class SLPArena:
    """Hash-consed balanced SLP/RLSLP arena."""

    __slots__ = (
        "_cat",
        "_rep",
        "_term",
        "_node_id_generation",
        "_node_storage_poisoned",
        "_node_storage_identity",
        "empty_id",
        "nodes",
    )

    nodes: MutableSequence[SLPNode]
    _node_storage_identity: MutableSequence[SLPNode]

    def __init__(self) -> None:
        if hasattr(self, "nodes") and not isinstance(self.nodes, SLPNodeStorage):
            raise TypeError("owned SLP storage requires its owner's reset protocol")
        try:
            self._invalidate_node_ids()
        except AttributeError:
            self._node_id_generation = 0
        self._node_storage_poisoned = False
        nodes: MutableSequence[SLPNode] = SLPNodeStorage(
            self._invalidate_external_node_mutation
        )
        object.__setattr__(self, "nodes", nodes)
        object.__setattr__(self, "_node_storage_identity", nodes)
        self._term: MutableMapping[int, int] = {}
        self._cat: MutableMapping[tuple[int, int], int] = {}
        self._rep: MutableMapping[tuple[int, int], int] = {}
        self.empty_id = self._add("EMPTY", 0)

    def __setattr__(self, name: str, value: object) -> None:
        if name == "nodes":
            try:
                current = object.__getattribute__(self, "nodes")
            except AttributeError:
                object.__setattr__(self, name, value)
                object.__setattr__(self, "_node_storage_identity", value)
                return
            else:
                if current is value:
                    return
                raise AttributeError("SLP node storage identity is immutable")
        object.__setattr__(self, name, value)

    def __reduce_ex__(self, protocol: SupportsIndex, /) -> Never:
        raise TypeError("SLP arena authority cannot be copied or serialized")

    @property
    def node_id_generation(self) -> int:
        """Monotone generation changed whenever existing node IDs are invalidated."""
        return self._node_id_generation

    def _invalidate_node_ids(self) -> None:
        self._node_id_generation += 1

    def _invalidate_external_node_mutation(self) -> None:
        self._invalidate_node_ids()
        self._node_storage_poisoned = True

    @property
    def node_storage_poisoned(self) -> bool:
        """Whether destructive public node edits invalidated its interners."""
        return (
            self._node_storage_poisoned or self.nodes is not self._node_storage_identity
        )

    def _require_coherent_interners(self) -> None:
        if self.node_storage_poisoned:
            raise RuntimeError("SLP node rows changed; canonical interners are stale")

    def find_terminal(self, symbol: int) -> int | None:
        """Look up a canonical terminal without allocating it."""
        self._require_coherent_interners()
        return self._term.get(symbol)

    def find_concat(self, left: int, right: int) -> int | None:
        """Look up an existing ordered concatenation without allocating it."""
        self._require_coherent_interners()
        return self._cat.get((left, right))

    def find_repeat(self, child: int, count: int) -> int | None:
        """Look up an existing canonical repeat without allocating it."""
        self._require_coherent_interners()
        return self._rep.get((child, count))

    def clear(self) -> None:
        """Release the grammar and its canonical lookup tables together."""
        if self.nodes or self._term or self._cat or self._rep:
            self._invalidate_node_ids()
            self._node_storage_poisoned = True
        self._term.clear()
        self._cat.clear()
        self._rep.clear()
        self.nodes.clear()

    def _add(self, kind: str, length: int, **kw: int) -> int:
        self._require_coherent_interners()
        q = len(self.nodes)
        self.nodes.append(SLPNode(q, kind, int(length), **kw))
        record_slp_metrics(nodes=1)
        return q

    def _add_interned(
        self,
        kind: str,
        length: int,
        table: MutableMapping[_InternKey, int],
        key: _InternKey,
        **kw: int,
    ) -> int:
        """Publish one interned node; subclasses may make this atomic/ledgered."""
        node = self._add(kind, length, **kw)
        table[key] = node
        return node

    def empty(self) -> int:
        """Return the empty-node ID without allocating or changing the arena."""
        return self.empty_id

    def terminal(self, symbol: int) -> int:
        self._require_coherent_interners()
        symbol = int(symbol)
        old = self._term.get(symbol)
        if old is not None:
            return old
        return self._add_interned("TERM", 1, self._term, symbol, symbol=symbol)

    def concat(self, left: int, right: int) -> int:
        self._require_coherent_interners()
        left, right = int(left), int(right)
        if left == self.empty_id:
            return right
        if right == self.empty_id:
            return left
        key = (left, right)
        old = self._cat.get(key)
        if old is not None:
            return old
        return self._add_interned(
            "CONCAT",
            self.nodes[left].length + self.nodes[right].length,
            self._cat,
            key,
            left=left,
            right=right,
        )

    def repeat(self, child: int, count: int) -> int:
        self._require_coherent_interners()
        child, count = int(child), int(count)
        key = canonical_repeat_key(self.nodes, self.empty_id, child, count)
        if isinstance(key, int):
            return key
        child, count = key
        n = self.nodes[child]
        old = self._rep.get(key)
        if old is not None:
            return old
        return self._add_interned(
            "REPEAT", n.length * count, self._rep, key, child=child, count=count
        )

    def concat_many(self, nodes: Iterable[int]) -> int:
        self._require_coherent_interners()
        row: list[int] = []
        nxt: list[int] = []
        try:
            for node in nodes:
                if int(node) != self.empty_id:
                    row.append(int(node))
            if not row:
                return self.empty_id
            # Pairwise balancing gives logarithmic derivation height for a flat list.
            while len(row) > 1:
                nxt.clear()
                for i in range(0, len(row), 2):
                    nxt.append(
                        self.concat(row[i], row[i + 1]) if i + 1 < len(row) else row[i]
                    )
                row.clear()
                row, nxt = nxt, row
            result = row[0]
            return result
        finally:
            row.clear()
            nxt.clear()

    def word(self, word: Sequence[int]) -> int:
        return self.concat_many(self.terminal(a) for a in word)

    def materialize(self, root: int) -> tuple[int, ...]:
        """Reference/debug expansion.  Powered code must not call this."""
        from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

        forbid_in_powered_jump("slp_materialize")
        out: list[int] = []
        stack: list[tuple[int, int]] = [(int(root), 1)]
        while stack:
            q, mult = stack.pop()
            n = self.nodes[q]
            if n.kind == "EMPTY":
                continue
            if n.kind == "TERM":
                out.extend([n.symbol] * mult)
            elif n.kind == "CONCAT":
                for _ in range(mult):
                    push_binary_children(stack, n, (n.left, 1), (n.right, 1))
            elif n.kind == "REPEAT":
                stack.append((n.child, mult * n.count))
            else:  # pragma: no cover - arena invariant
                raise AssertionError(n.kind)
        return tuple(out)

    def reachable(self, root: int) -> set[int]:
        seen: set[int] = set()
        todo = [int(root)]
        while todo:
            q = todo.pop()
            if q in seen:
                continue
            seen.add(q)
            n = self.nodes[q]
            if n.kind == "CONCAT":
                todo.extend((n.left, n.right))
            elif n.kind == "REPEAT":
                todo.append(n.child)
        return seen

    def metrics(self, root: int) -> SLPMetrics:
        reach = self.reachable(root)
        memo_depth: dict[int, int] = {}
        depth_stack: list[tuple[int, bool]] = [(int(root), False)]
        while depth_stack:
            q, expanded = depth_stack.pop()
            if q in memo_depth:
                continue
            n = self.nodes[q]
            if n.kind in ("EMPTY", "TERM"):
                memo_depth[q] = 1
                continue
            children = (n.left, n.right) if n.kind == "CONCAT" else (n.child,)
            if not expanded:
                depth_stack.append((q, True))
                for child in children:
                    if child not in memo_depth:
                        depth_stack.append((child, False))
                continue
            memo_depth[q] = 1 + max(memo_depth[child] for child in children)
        terminals = sum(self.nodes[q].kind == "TERM" for q in reach)
        concats = sum(self.nodes[q].kind == "CONCAT" for q in reach)
        repeats = sum(self.nodes[q].kind == "REPEAT" for q in reach)
        idbits = _bits(max(reach, default=0))
        desc = 0
        for q in reach:
            n = self.nodes[q]
            desc += 3 + _bits(n.length)
            if n.kind == "TERM":
                desc += _bits(n.symbol)
            elif n.kind == "CONCAT":
                desc += 2 * idbits
            elif n.kind == "REPEAT":
                desc += idbits + _bits(n.count)
        return SLPMetrics(
            self.nodes[int(root)].length,
            len(reach),
            terminals,
            concats,
            repeats,
            memo_depth[int(root)],
            desc,
        )


class BimachineSLPProjector:
    """Apply one exact bimachine to an SLP without decompressing the input."""

    __slots__ = (
        "__weakref__",
        "_block",
        "_fwd",
        "_fwd_power",
        "_rev",
        "_rev_power",
        "_cache_consumer_claim",
        "_cache_clear_failed",
        "_cache_stores_bound",
        "_initial_arena",
        "_initial_node_storage",
        "_arena_node_id_generation",
        "_initial_machine",
        "arena",
        "machine",
        "section_calls",
    )

    def __init__(self, machine: BimachineProtocol, arena: SLPArena) -> None:
        if arena.node_storage_poisoned:
            raise RuntimeError(
                "projector cannot bind an SLP arena with stale interners"
            )
        self.machine = machine
        self.arena = arena
        self._initial_machine = machine
        self._initial_arena = arena
        self._initial_node_storage = arena.nodes
        self._arena_node_id_generation = arena.node_id_generation
        self._fwd: MutableMapping[tuple[int, int], int | None] = {}
        self._rev: MutableMapping[tuple[int, int], int | None] = {}
        self._block: MutableMapping[tuple[int, int, int], int] = {}
        self._fwd_power: MutableMapping[tuple[int, int, int], int | None] = {}
        self._rev_power: MutableMapping[tuple[int, int, int], int | None] = {}
        self._cache_consumer_claim: object | None = None
        self._cache_clear_failed = False
        self._cache_stores_bound = False
        self.section_calls = 0

    def bind_cache_stores(
        self,
        *,
        forward: OwnedMemo[tuple[int, int], int | None],
        reverse: OwnedMemo[tuple[int, int], int | None],
        block: OwnedMemo[tuple[int, int, int], int],
        forward_power: OwnedMemo[tuple[int, int, int], int | None],
        reverse_power: OwnedMemo[tuple[int, int, int], int | None],
    ) -> None:
        """Bind five exact, ledger-owned stores before the first projection.

        Each memo receives one immutable consumer claim. This prevents another
        projector with different node or machine authority from reusing its
        node-ID keyed cache, even after the first projector clears its rows.
        Standalone projectors keep their private in-memory mappings.
        """
        from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
        from number_compiler.resources.owned_memo import OwnedMemo

        stores = (forward, reverse, block, forward_power, reverse_power)
        if (
            self.machine is not self._initial_machine
            or self.arena is not self._initial_arena
            or self.arena.nodes is not self._initial_node_storage
        ):
            raise RuntimeError(
                "projector machine or arena authority changed after construction"
            )
        self.arena.empty()
        if self.arena.node_id_generation != self._arena_node_id_generation:
            raise RuntimeError(
                "projector arena node IDs changed; clear caches before binding"
            )
        if self.arena.node_storage_poisoned:
            raise RuntimeError("projector SLP arena interners are stale")
        if (
            self._cache_stores_bound
            or self.section_calls
            or any(
                len(cache)
                for cache in (
                    self._fwd,
                    self._rev,
                    self._block,
                    self._fwd_power,
                    self._rev_power,
                )
            )
        ):
            raise ValueError("projector cache stores are already in use")
        if any(type(store) is not OwnedMemo for store in stores):
            raise TypeError("projector cache binding requires exact owned memos")
        if type(self.arena) is not LedgerSLPArena:
            raise TypeError("owned projector caches require a ledgered SLP arena")
        if any(
            left is right
            for index, left in enumerate(stores)
            for right in stores[index + 1 :]
        ):
            raise ValueError("projector cache stores must have distinct owners")
        if any(store.ledger is not self.arena.ledger for store in stores):
            raise ValueError("projector cache stores belong to another ledger")
        if len({store.owner for store in stores}) != len(stores):
            raise ValueError("projector cache stores require distinct resource owners")
        ledger = self.arena.ledger
        arena_owners = self.arena.owners
        if type(arena_owners) is not tuple or len(arena_owners) != 4:
            raise ValueError("projector arena owner binding is invalid")
        if any(ledger.account_status(owner).disposed for owner in arena_owners):
            raise ValueError("projector arena has a disposed resource owner")
        if any(len(store) for store in stores):
            raise ValueError("projector cache stores must be empty at binding")
        previous_stores = (
            self._fwd,
            self._rev,
            self._block,
            self._fwd_power,
            self._rev_power,
        )
        try:
            with OwnedMemo.claim_empty_consumer(
                cast(tuple[OwnedMemo[object, object], ...], stores),
                ledger=ledger,
                consumer=self,
            ) as claim:
                self._fwd = forward
                self._rev = reverse
                self._block = block
                self._fwd_power = forward_power
                self._rev_power = reverse_power
                self._cache_consumer_claim = claim
                self._cache_stores_bound = True
        except BaseException:
            (
                self._fwd,
                self._rev,
                self._block,
                self._fwd_power,
                self._rev_power,
            ) = previous_stores
            self._cache_consumer_claim = None
            self._cache_stores_bound = False
            raise

    @property
    def audit_cache_binding_identity(self) -> object | None:
        """Expose the opaque shared claim identity to forensic owner audits."""
        return self._cache_consumer_claim

    def has_exact_owned_cache_binding(
        self,
        *,
        forward: object,
        reverse: object,
        block: object,
        forward_power: object,
        reverse_power: object,
    ) -> bool:
        """Check backing identities and the shared committed claim for audits."""
        from number_compiler.resources.owned_memo import OwnedMemo

        caches = (
            self._fwd,
            self._rev,
            self._block,
            self._fwd_power,
            self._rev_power,
        )
        expected = (forward, reverse, block, forward_power, reverse_power)
        claim = self._cache_consumer_claim
        if (
            not self._cache_stores_bound
            or self.machine is not self._initial_machine
            or self.arena is not self._initial_arena
            or self.arena.nodes is not self._initial_node_storage
            or claim is None
            or any(type(cache) is not OwnedMemo for cache in caches)
        ):
            return False
        arena_open = self._arena_is_open()
        retired = True
        for cache, backing_store in zip(caches, expected, strict=True):
            memo = cast(OwnedMemo[object, object], cache)
            snapshot = memo.audit_snapshot()
            if type(backing_store) is OwnedMemo:
                expected_memo = cast(OwnedMemo[object, object], backing_store)
                if cache is not expected_memo:
                    return False
                if snapshot.container is not expected_memo.audit_snapshot().container:
                    return False
            else:
                if snapshot.container is not backing_store:
                    return False
            if (
                snapshot.consumer_claim_identity is not claim
                or not snapshot.consumer_claim_committed
                or snapshot.consumer is not self
            ):
                return False
            retired = retired and snapshot.disposed and len(snapshot.container) == 0
        if arena_open:
            if self._cache_clear_failed:
                return False
            return self.arena.node_id_generation == self._arena_node_id_generation
        return retired

    @property
    def audit_cache_stores(
        self,
    ) -> tuple[
        SLPCacheAuditView[tuple[int, int]],
        SLPCacheAuditView[tuple[int, int]],
        SLPCacheAuditView[tuple[int, int, int]],
        SLPCacheAuditView[tuple[int, int, int]],
        SLPCacheAuditView[tuple[int, int, int]],
    ]:
        """Return read-only views of the exact five projector cache stores."""
        return (
            slp_cache_audit_view(self._fwd),
            slp_cache_audit_view(self._rev),
            slp_cache_audit_view(self._block),
            slp_cache_audit_view(self._fwd_power),
            slp_cache_audit_view(self._rev_power),
        )

    def clear_caches(self) -> None:
        """Release retained state and block actions while preserving the arena.

        Projector caches can contain SLP node identifiers that a caller is
        about to roll back. Clearing all five stores keeps the projector safe
        for reuse and releases any ledger-backed cache charges.
        """
        from number_compiler.resources.lifecycle import cleanup_all

        self._cache_clear_failed = True
        cleanup_all(
            cache.clear
            for cache in (
                self._fwd,
                self._rev,
                self._block,
                self._fwd_power,
                self._rev_power,
            )
        )
        self._cache_clear_failed = False
        if (
            self.machine is self._initial_machine
            and self.arena is self._initial_arena
            and self.arena.nodes is self._initial_node_storage
            and self._arena_is_open()
        ):
            self._arena_node_id_generation = self.arena.node_id_generation

    def _arena_is_open(self) -> bool:
        if (
            self.arena is not self._initial_arena
            or self.arena.nodes is not self._initial_node_storage
            or self.arena.node_storage_poisoned
        ):
            return False
        try:
            self.arena.empty()
        except ValueError:
            return False
        return True

    def _check_cache_ready(self) -> None:
        if self._cache_clear_failed:
            raise RuntimeError(
                "projector cache clear failed; retry clearing before reuse"
            )
        if (
            self.machine is not self._initial_machine
            or self.arena is not self._initial_arena
            or self.arena.nodes is not self._initial_node_storage
        ):
            raise RuntimeError(
                "projector machine or arena authority changed after construction"
            )
        self.arena.empty()
        if self.arena.node_id_generation != self._arena_node_id_generation:
            raise RuntimeError(
                "projector arena node IDs changed; clear caches before reuse"
            )
        if self.arena.node_storage_poisoned:
            raise RuntimeError("projector SLP arena interners are stale")

    def _action(self, q: int, state: int, *, right: bool) -> int | None:
        self._check_cache_ready()
        node_cache = self._rev if right else self._fwd
        power_cache = self._rev_power if right else self._fwd_power
        root_key = (int(q), int(state))
        if root_key in node_cache:
            return node_cache[root_key]

        tasks: list[tuple[str, *tuple[int, ...]]] = [("NODE", int(q), int(state))]
        values: list[int | None] = []
        try:
            while tasks:
                task = tasks.pop()
                tag = task[0]
                if tag == "NODE":
                    node_id, st = task[1:]
                    key = (node_id, st)
                    if key in node_cache:
                        values.append(node_cache[key])
                        continue
                    n = self.arena.nodes[node_id]
                    if n.kind == "EMPTY":
                        out: int | None = st
                        node_cache[key] = out
                        values.append(out)
                    elif n.kind == "TERM":
                        out = (
                            self.machine.right.step(st, n.symbol)
                            if right
                            else self.machine.left.step(st, n.symbol)
                        )
                        node_cache[key] = out
                        values.append(out)
                    elif n.kind == "CONCAT":
                        first, second = (
                            (n.right, n.left) if right else (n.left, n.right)
                        )
                        tasks.append(("NODE_AFTER_FIRST", node_id, st, second))
                        tasks.append(("NODE", first, st))
                    elif n.kind == "REPEAT":
                        tasks.append(("NODE_STORE", node_id, st))
                        tasks.append(("REPEAT", n.child, st, n.count))
                    else:  # pragma: no cover
                        raise AssertionError(n.kind)
                elif tag == "NODE_AFTER_FIRST":
                    node_id, st, second = task[1:]
                    mid = values.pop()
                    if mid is None:
                        out = None
                        node_cache[(node_id, st)] = out
                        values.append(out)
                    else:
                        tasks.append(("NODE_STORE", node_id, st))
                        tasks.append(("NODE", second, mid))
                elif tag == "NODE_STORE":
                    node_id, st = task[1:]
                    out = values.pop()
                    node_cache[(node_id, st)] = out
                    values.append(out)
                elif tag == "REPEAT":
                    child, st, count = task[1:]
                    power_key = (child, st, count)
                    if power_key in power_cache:
                        values.append(power_cache[power_key])
                        continue
                    if count == 0:
                        power_cache[power_key] = st
                        values.append(st)
                    elif count == 1:
                        tasks.append(("REPEAT_STORE", child, st, count))
                        tasks.append(("NODE", child, st))
                    else:
                        half = count // 2
                        tasks.append(("REPEAT_AFTER_HALF", child, st, count, half))
                        tasks.append(("REPEAT", child, st, half))
                elif tag == "REPEAT_AFTER_HALF":
                    child, st, count, half = task[1:]
                    mid = values.pop()
                    if mid is None:
                        power_cache[(child, st, count)] = None
                        values.append(None)
                    else:
                        tasks.append(("REPEAT_AFTER_DOUBLE", child, st, count))
                        tasks.append(("REPEAT", child, mid, half))
                elif tag == "REPEAT_AFTER_DOUBLE":
                    child, st, count = task[1:]
                    twice = values.pop()
                    if count & 1 and twice is not None:
                        tasks.append(("REPEAT_STORE", child, st, count))
                        tasks.append(("NODE", child, twice))
                    else:
                        power_cache[(child, st, count)] = twice
                        values.append(twice)
                elif tag == "REPEAT_STORE":
                    child, st, count = task[1:]
                    out = values.pop()
                    power_cache[(child, st, count)] = out
                    values.append(out)
                else:  # pragma: no cover
                    raise AssertionError(tag)
            if len(values) != 1:
                raise AssertionError(values)
            return values[0]
        finally:
            tasks.clear()
            values.clear()

    def forward(self, q: int, state: int) -> int | None:
        return self._action(int(q), int(state), right=False)

    def reverse(self, q: int, state: int) -> int | None:
        return self._action(int(q), int(state), right=True)

    def block(self, q: int, left: int, right: int) -> int:
        self._check_cache_ready()
        root = (int(q), int(left), int(right))
        old = self._block.get(root)
        if old is not None:
            return old
        tasks: list[tuple[str, *tuple[int, ...]]] = [("BLOCK", *root)]
        values: list[int] = []
        positions: list[int] = []
        parts: list[int] = []
        middle: list[int] = []
        prefix_parts: list[int] = []
        suffix_parts: list[int] = []
        tail_parts: list[int] = []
        left_orbit: list[int] = []
        right_orbit: list[int] = []
        try:
            while tasks:
                task = tasks.pop()
                tag = task[0]
                if tag == "BLOCK":
                    node_id, lctx, rctx = task[1:]
                    key = (node_id, lctx, rctx)
                    cached = self._block.get(key)
                    if cached is not None:
                        values.append(cached)
                        continue
                    self.section_calls += 1
                    record_slp_metrics(sections=1)
                    n = self.arena.nodes[node_id]
                    if n.kind == "EMPTY":
                        out = self.arena.empty()
                        self._block[key] = out
                        values.append(out)
                    elif n.kind == "TERM":
                        word = self.machine.emit(lctx, n.symbol, rctx)
                        if word is None:
                            raise ValueError(
                                ("undefined bimachine output", lctx, n.symbol, rctx)
                            )
                        out = self.arena.word(word)
                        self._block[key] = out
                        values.append(out)
                    elif n.kind == "CONCAT":
                        child_left, child_right = transduction_midpoints(
                            self.forward, self.reverse, n.left, n.right, lctx, rctx
                        )
                        tasks.append(("BLOCK_CONCAT", node_id, lctx, rctx))
                        tasks.append(("BLOCK", n.right, child_left, rctx))
                        tasks.append(("BLOCK", n.left, lctx, child_right))
                    elif n.kind == "REPEAT":
                        tasks.append(("BLOCK_STORE", node_id, lctx, rctx))
                        tasks.append(("REPEAT_BLOCK", n.child, n.count, lctx, rctx))
                    else:  # pragma: no cover
                        raise AssertionError(n.kind)
                elif tag == "BLOCK_CONCAT":
                    node_id, lctx, rctx = task[1:]
                    right_out = values.pop()
                    left_out = values.pop()
                    out = self.arena.concat(left_out, right_out)
                    self._block[(node_id, lctx, rctx)] = out
                    values.append(out)
                elif tag == "BLOCK_STORE":
                    node_id, lctx, rctx = task[1:]
                    out = values.pop()
                    self._block[(node_id, lctx, rctx)] = out
                    values.append(out)
                elif tag == "REPEAT_BLOCK":
                    child, count, lctx, rctx = task[1:]
                    if count == 0:
                        values.append(self.arena.empty())
                    elif count == 1:
                        tasks.append(("BLOCK", child, lctx, rctx))
                    else:
                        # The j-th copy is emitted from both its left and right
                        # contexts. Their DFA orbits are finite, so once both
                        # have entered their cycles the paired emission repeats.
                        # Recursively splitting the exponent would still visit
                        # every copy here, despite powering the DFA actions.
                        left_orbit, left_mu, left_period = self._context_orbit(
                            child, lctx, count=count, right=False
                        )
                        right_orbit, right_mu, right_period = self._context_orbit(
                            child, rctx, count=count, right=True
                        )
                        prefix_count = min(count, left_mu)
                        suffix_count = min(count - prefix_count, right_mu)
                        middle_count = count - prefix_count - suffix_count
                        cycle_count = lcm(left_period, right_period)
                        pattern_count = min(middle_count, cycle_count)
                        repeated, tail_count = divmod(middle_count, cycle_count)
                        if repeated == 0:
                            pattern_count = 0
                            tail_count = middle_count

                        # Materialize at most the two finite transients, one
                        # paired-context cycle, and its tail. Right contexts are
                        # indexed from the far end of the repeated source.
                        middle_samples = pattern_count or tail_count
                        positions.extend(range(prefix_count))
                        positions.extend(
                            range(prefix_count, prefix_count + middle_samples)
                        )
                        positions.extend(range(count - suffix_count, count))
                        tasks.append(
                            (
                                "REPEAT_FINISH_CYCLES",
                                prefix_count,
                                middle_samples,
                                repeated,
                                tail_count,
                                suffix_count,
                                pattern_count,
                            )
                        )
                        for index in reversed(positions):
                            left_state = self._orbit_at(
                                left_orbit, left_mu, left_period, index
                            )
                            right_state = self._orbit_at(
                                right_orbit,
                                right_mu,
                                right_period,
                                count - 1 - index,
                            )
                            tasks.append(("BLOCK", child, left_state, right_state))
                        positions.clear()
                        left_orbit.clear()
                        right_orbit.clear()
                elif tag == "REPEAT_FINISH_CYCLES":
                    (
                        prefix_count,
                        middle_samples,
                        repeated,
                        tail_count,
                        suffix_count,
                        pattern_count,
                    ) = task[1:]
                    total = prefix_count + middle_samples + suffix_count
                    parts.extend(values[-total:] if total else ())
                    if total:
                        del values[-total:]
                    prefix_parts.extend(parts[:prefix_count])
                    middle.extend(parts[prefix_count : prefix_count + middle_samples])
                    suffix_parts.extend(parts[prefix_count + middle_samples :])
                    prefix = self.arena.concat_many(prefix_parts)
                    suffix = self.arena.concat_many(suffix_parts)
                    if pattern_count:
                        cycle = self.arena.concat_many(middle)
                        tail_parts.extend(middle[:tail_count])
                        body = self.arena.concat(
                            self.arena.repeat(cycle, repeated),
                            self.arena.concat_many(tail_parts),
                        )
                    else:
                        body = self.arena.concat_many(middle)
                    values.append(self.arena.concat_many((prefix, body, suffix)))
                    parts.clear()
                    middle.clear()
                    prefix_parts.clear()
                    suffix_parts.clear()
                    tail_parts.clear()
                else:  # pragma: no cover
                    raise AssertionError(tag)
            if len(values) != 1:
                raise AssertionError(values)
            return values[0]
        finally:
            tasks.clear()
            values.clear()
            positions.clear()
            parts.clear()
            middle.clear()
            prefix_parts.clear()
            suffix_parts.clear()
            tail_parts.clear()
            left_orbit.clear()
            right_orbit.clear()

    def _context_orbit(
        self, child: int, start: int, *, count: int, right: bool
    ) -> tuple[list[int], int, int]:
        """Return the demanded prefix plus its exact finite-state cycle.

        A partial DFA transition after the final requested copy is irrelevant
        and is not evaluated. A missing transition before another copy is
        needed fails closed.
        """
        seen: dict[int, int] = {}
        states: list[int] = []
        state = start
        try:
            while state not in seen and len(states) < count:
                seen[state] = len(states)
                states.append(state)
                if len(states) == count:
                    orbit = states
                    states = []
                    return orbit, len(orbit), 1
                successor = self._action(child, state, right=right)
                if successor is None:
                    raise ValueError("context reject in repeat")
                state = successor
            mu = seen[state]
            period = len(states) - mu
            orbit = states
            states = []
            return orbit, mu, period
        finally:
            seen.clear()
            states.clear()

    @staticmethod
    def _orbit_at(states: Sequence[int], mu: int, period: int, index: int) -> int:
        if index < mu:
            return states[index]
        return states[mu + (index - mu) % period]

    def apply(self, root: int) -> int:
        return self.block(int(root), self.machine.left.start, self.machine.right.start)


__all__ = [
    "BimachineSLPProjector",
    "SLPArena",
    "SLPMetrics",
    "SLPNode",
    "canonical_repeat_key",
]
