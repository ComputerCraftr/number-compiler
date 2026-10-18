"""Balanced straight-line programs and exact regular-transduction projection.

This module is compiler metadata only.  It implements the spatial projection
primitive justified by the closure of SLP-compressed strings under regular
transductions: a finite bimachine is applied directly to a hash-consed grammar,
without expanding the represented word.

``REPEAT`` nodes are first-class.  DFA actions over a repeated block are powered
by binary exponentiation, and output projection recursively splits only the
repeat exponent, never the represented characters.
"""

from __future__ import annotations

from collections.abc import Iterable, MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass
from typing import Protocol, TypeVar

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.transducer import (
    transduction_midpoints,
)
from number_compiler.arithmetic.contracts.iterative_queries import push_binary_children
from number_compiler.arithmetic.fields.radix import bit_width

_bits = bit_width
_InternKey = TypeVar("_InternKey")


class _StateStart(Protocol):
    @property
    def start(self) -> int: ...

    def step(self, state: int, symbol: int) -> int | None: ...


class _SLPTransducer(Protocol):
    @property
    def left(self) -> _StateStart: ...

    @property
    def right(self) -> _StateStart: ...

    def emit(self, left: int, symbol: int, right: int, /) -> tuple[int, ...] | None: ...


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

    __slots__ = ("_cat", "_rep", "_term", "empty_id", "nodes")

    def __init__(self) -> None:
        self.nodes: MutableSequence[SLPNode] = []
        self._term: MutableMapping[int, int] = {}
        self._cat: MutableMapping[tuple[int, int], int] = {}
        self._rep: MutableMapping[tuple[int, int], int] = {}
        self.empty_id = self._add("EMPTY", 0)

    def _add(self, kind: str, length: int, **kw: int) -> int:
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
        return self.empty_id

    def terminal(self, symbol: int) -> int:
        symbol = int(symbol)
        old = self._term.get(symbol)
        if old is not None:
            return old
        return self._add_interned("TERM", 1, self._term, symbol, symbol=symbol)

    def concat(self, left: int, right: int) -> int:
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
        row = [int(q) for q in nodes if int(q) != self.empty_id]
        if not row:
            return self.empty_id
        # Pairwise balancing gives logarithmic derivation height for a flat list.
        while len(row) > 1:
            nxt: list[int] = []
            for i in range(0, len(row), 2):
                nxt.append(
                    self.concat(row[i], row[i + 1]) if i + 1 < len(row) else row[i]
                )
            row = nxt
        return row[0]

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
        "_block",
        "_fwd",
        "_fwd_power",
        "_rev",
        "_rev_power",
        "arena",
        "machine",
        "section_calls",
    )

    def __init__(self, machine: _SLPTransducer, arena: SLPArena):
        self.machine = machine
        self.arena = arena
        self._fwd: MutableMapping[tuple[int, int], int | None] = {}
        self._rev: MutableMapping[tuple[int, int], int | None] = {}
        self._block: MutableMapping[tuple[int, int, int], int] = {}
        self._fwd_power: MutableMapping[tuple[int, int, int], int | None] = {}
        self._rev_power: MutableMapping[tuple[int, int, int], int | None] = {}
        self.section_calls = 0

    def _action(self, q: int, state: int, *, right: bool) -> int | None:
        node_cache = self._rev if right else self._fwd
        power_cache = self._rev_power if right else self._fwd_power
        root_key = (int(q), int(state))
        if root_key in node_cache:
            return node_cache[root_key]

        tasks: list[tuple[str, *tuple[int, ...]]] = [("NODE", int(q), int(state))]
        values: list[int | None] = []
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
                    first, second = (n.right, n.left) if right else (n.left, n.right)
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

    def _repeat_action(
        self, q: int, state: int, count: int, *, right: bool
    ) -> int | None:
        # Compatibility wrapper; the implementation is an explicit work stack.
        cache = self._rev_power if right else self._fwd_power
        key = (int(q), int(state), int(count))
        if key in cache:
            return cache[key]
        tasks: list[tuple[str, *tuple[int, ...]]] = [
            ("REPEAT", int(q), int(state), int(count))
        ]
        values: list[int | None] = []
        # Reuse _action for child actions while keeping exponent decomposition iterative.
        while tasks:
            frame = tasks.pop()
            tag = frame[0]
            child, st, c, *rest = frame[1:]
            key = (child, st, c)
            if tag == "REPEAT":
                if key in cache:
                    values.append(cache[key])
                    continue
                if c == 0:
                    cache[key] = st
                    values.append(st)
                    continue
                if c == 1:
                    out = self._action(child, st, right=right)
                    cache[key] = out
                    values.append(out)
                    continue
                half = c // 2
                tasks.append(("AFTER_HALF", child, st, c, half))
                tasks.append(("REPEAT", child, st, half))
            elif tag == "AFTER_HALF":
                half = rest[0]
                mid = values.pop()
                if mid is None:
                    cache[key] = None
                    values.append(None)
                    continue
                tasks.append(("AFTER_DOUBLE", child, st, c))
                tasks.append(("REPEAT", child, mid, half))
            elif tag == "AFTER_DOUBLE":
                twice = values.pop()
                if c & 1 and twice is not None:
                    twice = self._action(child, twice, right=right)
                cache[key] = twice
                values.append(twice)
            else:  # pragma: no cover
                raise AssertionError(tag)
        return values.pop()

    def forward(self, q: int, state: int) -> int | None:
        return self._action(int(q), int(state), right=False)

    def reverse(self, q: int, state: int) -> int | None:
        return self._action(int(q), int(state), right=True)

    def block(self, q: int, left: int, right: int) -> int:
        root = (int(q), int(left), int(right))
        old = self._block.get(root)
        if old is not None:
            return old
        tasks: list[tuple[str, *tuple[int, ...]]] = [("BLOCK", *root)]
        values: list[int] = []
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
                    a = count // 2
                    b = count - a
                    left_mid = self._repeat_action(child, lctx, a, right=False)
                    right_mid = self._repeat_action(child, rctx, b, right=True)
                    if left_mid is None or right_mid is None:
                        raise ValueError("context reject in repeat")
                    tasks.append(("REPEAT_COMBINE", a, b))
                    tasks.append(("REPEAT_BLOCK", child, b, left_mid, rctx))
                    tasks.append(("REPEAT_BLOCK", child, a, lctx, right_mid))
            elif tag == "REPEAT_COMBINE":
                a, b = task[1:]
                y = values.pop()
                x = values.pop()
                values.append(
                    self.arena.repeat(x, 2)
                    if a == b and x == y
                    else self.arena.concat(x, y)
                )
            else:  # pragma: no cover
                raise AssertionError(tag)
        if len(values) != 1:
            raise AssertionError(values)
        return values[0]

    def apply(self, root: int) -> int:
        return self.block(int(root), self.machine.left.start, self.machine.right.start)


__all__ = [
    "BimachineSLPProjector",
    "SLPArena",
    "SLPMetrics",
    "SLPNode",
    "canonical_repeat_key",
]
