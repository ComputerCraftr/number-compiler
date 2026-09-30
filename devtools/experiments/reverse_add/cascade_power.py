"""Bounded reference construction of universal bimachine contexts.

Classical bimachine composition determinizes subsets of Cartesian triples.  This
module keeps those subsets as reduced selector MDDs (dependency cascades) and
computes transitions by bitset/group operations. Avoiding a flat tuple universe
does not make this the source-ray semantic action quotient. Decimal production
must not use this construction or minimize its contexts to establish closure.

A complete pair of context DFAs can be wrapped as an exact ``LazyBimachine``.
Capped/incomplete compilations are diagnostics only and cannot be promoted to a
jump backend. Even complete contexts do not establish a source-bound return.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Callable, Iterable, Iterator, Sequence
from dataclasses import dataclass
from time import perf_counter
from typing import (
    TypeVar,
    cast,
)

from devtools.experiments.reverse_add.cascade import (
    CascadeRelation,
    GroupedDependencyCascadeArena,
    group_left_behavior,
)
from devtools.experiments.reverse_add.power import _fragment
from number_compiler.arithmetic.automata.transducer import DFA, LazyBimachine

_Word = tuple[int, ...]
_Regions = tuple[tuple[_Word, int, int], ...]
_CacheKey = TypeVar("_CacheKey")
_CacheValue = TypeVar("_CacheValue")


def _values(mask: int) -> Iterator[int]:
    x = int(mask)
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


@dataclass(frozen=True, slots=True)
class CascadeContextMetrics:
    states: int
    dependency_nodes: int
    dependency_groups: int
    description_bits: int
    represented_tuples: int
    seconds: float
    complete: bool


@dataclass(slots=True)
class CascadeContextDFA:
    alphabet: tuple[int, ...]
    start: int
    trans: dict[tuple[int, int], int]
    states: tuple[int, ...]
    relations: tuple[CascadeRelation, ...]
    arena: GroupedDependencyCascadeArena
    right: bool
    complete: bool
    seconds: float

    def step(self, q: int, symbol: int) -> int | None:
        return self.trans.get((int(q), int(symbol)))

    def word(self, q: int, word: Sequence[int]) -> int | None:
        seq = reversed(tuple(word)) if self.right else word
        out = int(q)
        for a in seq:
            z = self.step(out, int(a))
            if z is None:
                return None
            out = z
        return out

    def boxes(self, q: int) -> Iterator[tuple[int, ...]]:
        return self.arena.iter_boxes(self.relations[int(q)])

    def metrics(self) -> CascadeContextMetrics:
        m = self.arena.metrics()
        return CascadeContextMetrics(
            len(self.states),
            m.dependency_nodes,
            m.dependency_edges,
            m.description_bits,
            sum(r.cardinality for r in self.relations),
            self.seconds,
            self.complete,
        )


class _RelationStates:
    __slots__ = ("arena", "by_root", "relations")

    def __init__(self, domains: Sequence[int], order: Sequence[int]) -> None:
        self.arena = GroupedDependencyCascadeArena(3, domains, order)
        self.by_root: dict[int, int] = {}
        self.relations: list[CascadeRelation] = []

    def intern(self, boxes: Iterable[Sequence[int]]) -> int:
        rel = self.arena.encode_boxes(boxes)
        old = self.by_root.get(rel.root)
        if old is not None:
            return old
        q = len(self.relations)
        self.by_root[rel.root] = q
        self.relations.append(rel)
        return q

    def boxes(self, q: int) -> Iterator[tuple[int, ...]]:
        return self.arena.iter_boxes(self.relations[int(q)])


class _Behavior:
    __slots__ = (
        "emit",
        "first",
        "left_classes",
        "left_image",
        "left_preimage",
        "left_symbol_image",
        "output_regions",
        "pred_right",
        "right_emit_classes",
        "right_image",
        "right_symbol_image",
        "second",
    )

    def __init__(self, first: LazyBimachine, second: LazyBimachine) -> None:
        self.first = first
        self.second = second
        self.emit: dict[tuple[int, int, int], _Word | None] = {}
        self.left_classes: dict[
            tuple[int, int], tuple[tuple[int, _Word, int], ...]
        ] = {}
        self.left_image: dict[tuple[int, _Word], int] = {}
        self.right_image: dict[tuple[int, _Word], int] = {}
        self.pred_right: dict[tuple[int, int], int] = {}
        # Preimage masks for the deterministic left transition of the first machine.
        self.left_preimage: dict[int, tuple[int, ...]] = {}
        for a in first.alphabet:
            inv = [0] * len(first.left.states)
            for left_state in first.left.states:
                z = first.left.step(left_state, a)
                if z is not None:
                    inv[z] |= 1 << left_state
            self.left_preimage[a] = tuple(inv)
        # For fixed (symbol,right-after), output word partitions the source-left
        # states.  Filtering an arbitrary target-left selector then becomes one
        # DFA preimage plus bitset intersections, not a scan cached by giant mask.
        self.right_emit_classes: dict[
            tuple[int, int], tuple[tuple[tuple[int, ...], int], ...]
        ] = {}
        self.output_regions: dict[
            int, tuple[tuple[tuple[int, ...], int, int], ...]
        ] = {}
        self.left_symbol_image: dict[tuple[int, int], int] = {}
        self.right_symbol_image: dict[tuple[int, int], int] = {}

    def E(self, left_state: int, a: int, r: int) -> _Word | None:
        k = (int(left_state), int(a), int(r))
        if self.first.has_canonical_output:
            return self.first.emit(*k)
        if k not in self.emit:
            self.emit[k] = self.first.emit(*k)
        return self.emit[k]

    @staticmethod
    def _bounded(
        cache: dict[_CacheKey, _CacheValue],
        key: _CacheKey,
        make: Callable[[], _CacheValue],
        cap: int = 4096,
    ) -> _CacheValue:
        if key in cache:
            return cache[key]
        out = make()
        if len(cache) >= cap:
            # FIFO-ish bounded memoization; dict insertion order is deterministic.
            cache.pop(next(iter(cache)))
        cache[key] = out
        return out

    def canonical_output_regions(self, a: int) -> _Regions:
        """Exact output-word boxes for fixed input symbol, without context scans."""
        a = int(a)
        old = self.output_regions.get(a)
        if old is not None:
            return old
        relation = self.first.canonical_output
        if relation is None:
            # Fallback is used only for small uncanonicalized research machines.
            # Production powers install a canonical output relation first.
            by_word: defaultdict[_Word, list[tuple[int, int]]] = defaultdict(list)
            for left_state in self.first.left.states:
                for r in self.first.right.states:
                    w = self.E(left_state, a, r)
                    if w is not None:
                        by_word[w].append((left_state, r))
            regions = []
            for w, pairs in by_word.items():
                # singleton boxes preserve exactness without attempting biclique cover.
                for left_state, r in pairs:
                    regions.append((w, 1 << left_state, 1 << r))
            out = tuple(regions)
        else:
            out = tuple(
                (tuple(w), int(sel[0]), int(sel[2]))
                for w, sel in cast(
                    Iterable[tuple[_Word, tuple[int, int, int]]],
                    relation.iter_boxes(symbol=a, include_undefined=False),
                )
            )
        self.output_regions[a] = out
        return out

    def image_left_symbol_mask(self, a: int, mask: int) -> int:
        key = (int(a), int(mask))

        def make() -> int:
            out = 0
            x = int(mask)
            while x:
                b = x & -x
                q = b.bit_length() - 1
                x ^= b
                z = self.first.left.step(q, int(a))
                if z is not None:
                    out |= 1 << z
            return out

        return self._bounded(self.left_symbol_image, key, make)

    def image_right_symbol_mask(self, a: int, mask: int) -> int:
        key = (int(a), int(mask))

        def make() -> int:
            out = 0
            x = int(mask)
            while x:
                b = x & -x
                q = b.bit_length() - 1
                x ^= b
                z = self.first.right.step(q, int(a))
                if z is not None:
                    out |= 1 << z
            return out

        return self._bounded(self.right_symbol_image, key, make)

    def predecessor_right_mask(self, a: int, before_mask: int) -> int:
        key = (int(a), int(before_mask))

        def make() -> int:
            out = 0
            for after in self.first.right.states:
                before = self.first.right.step(after, a)
                if before is not None and ((before_mask >> before) & 1):
                    out |= 1 << after
            return out

        return self._bounded(self.pred_right, key, make)

    def left_behavior(
        self, a: int, right_after: int
    ) -> tuple[tuple[int, _Word, int], ...]:
        k = (int(a), int(right_after))
        old = self.left_classes.get(k)
        if old is not None:
            return old
        out = group_left_behavior(
            self.first.left.states, self.first.left.step, self.E, a, right_after
        )
        self.left_classes[k] = out
        return out

    def _preimage_left_mask(self, a: int, target_mask: int) -> int:
        inv = self.left_preimage[a]
        out = 0
        x = int(target_mask)
        while x:
            b = x & -x
            t = b.bit_length() - 1
            x ^= b
            out |= inv[t]
        return out

    def image_left(self, mask: int, word: Sequence[int]) -> int:
        key = (int(mask), tuple(word))

        def make() -> int:
            out = 0
            for q in _values(mask):
                z = self.second.left.word(q, word)
                if z is not None:
                    out |= 1 << z
            return out

        return self._bounded(self.left_image, key, make)

    def _right_classes(self, a: int, right_after: int) -> tuple[tuple[_Word, int], ...]:
        key = (int(a), int(right_after))
        old = self.right_emit_classes.get(key)
        if old is not None:
            return old
        groups: defaultdict[_Word, int] = defaultdict(int)
        for left_state in self.first.left.states:
            if self.first.left.step(left_state, a) is None:
                continue
            v = self.E(left_state, a, right_after)
            if v is not None:
                groups[v] |= 1 << left_state
        out = tuple(groups.items())
        self.right_emit_classes[key] = out
        return out

    def right_behavior(
        self, a: int, right_after: int, left_after_mask: int
    ) -> tuple[tuple[_Word, int], ...]:
        allowed = self._preimage_left_mask(a, left_after_mask)
        return tuple(
            (v, mask & allowed)
            for v, mask in self._right_classes(a, right_after)
            if mask & allowed
        )

    def image_right(self, mask: int, word: Sequence[int]) -> int:
        key = (int(mask), tuple(word))

        def make() -> int:
            out = 0
            for q in _values(mask):
                z = self.second.right.word(q, word)
                if z is not None:
                    out |= 1 << z
            return out

        return self._bounded(self.right_image, key, make)


def _limit(
    start: float, nstates: int, state_cap: int | None, time_cap: float | None
) -> bool:
    return (state_cap is not None and nstates >= state_cap) or (
        time_cap is not None and perf_counter() - start >= time_cap
    )


def _walk_context(
    S: _RelationStates,
    C: _Behavior,
    alphabet: Sequence[int],
    start: int,
    *,
    state_cap: int | None,
    time_cap: float | None,
    right: bool,
) -> tuple[dict[tuple[int, int], int], bool, float]:
    trans: dict[tuple[int, int], int] = {}
    todo = deque([start])
    seen: set[int] = set()
    t0 = perf_counter()
    capped = False
    while todo:
        if _limit(t0, len(S.relations), state_cap, time_cap):
            capped = True
            break
        q = todo.popleft()
        if q in seen:
            continue
        seen.add(q)
        boxes = tuple(S.boxes(q))
        for a in alphabet:
            out = []
            regions = C.canonical_output_regions(a)
            if right:
                for l_after_mask, r2_after_mask, r_after_mask in boxes:
                    pre_l = C._preimage_left_mask(a, l_after_mask)
                    if not pre_l:
                        continue
                    for v, emit_lmask, emit_rmask in regions:
                        l_before = pre_l & emit_lmask
                        src_r = r_after_mask & emit_rmask
                        if not l_before or not src_r:
                            continue
                        r_before = C.image_right_symbol_mask(a, src_r)
                        r2_before = C.image_right(r2_after_mask, v)
                        if r_before and r2_before:
                            out.append((l_before, r2_before, r_before))
            else:
                for l1mask, l2mask, r_before_mask in boxes:
                    compatible_r = C.predecessor_right_mask(a, r_before_mask)
                    if not compatible_r:
                        continue
                    for v, emit_lmask, emit_rmask in regions:
                        src_l = l1mask & emit_lmask
                        r_after = compatible_r & emit_rmask
                        if not src_l or not r_after:
                            continue
                        l1_after = C.image_left_symbol_mask(a, src_l)
                        l2_after = C.image_left(l2mask, v)
                        if l1_after and l2_after:
                            out.append((l1_after, l2_after, r_after))
            if not out:
                continue
            z = S.intern(out)
            trans[q, a] = z
            if z not in seen:
                todo.append(z)
            if _limit(t0, len(S.relations), state_cap, time_cap):
                capped = True
                break
        if capped:
            break
    return trans, capped, perf_counter() - t0


def build_left_context(
    first: LazyBimachine,
    second: LazyBimachine,
    *,
    order: Sequence[int] = (0, 1, 2),
    state_cap: int | None = None,
    time_cap: float | None = None,
) -> CascadeContextDFA:
    if first.alphabet != second.alphabet:
        raise ValueError("alphabet mismatch")
    A = first.alphabet
    S = _RelationStates(
        (len(first.left.states), len(second.left.states), len(first.right.states)),
        order,
    )
    C = _Behavior(first, second)
    all_right = (1 << len(first.right.states)) - 1
    start = S.intern(((1 << first.left.start, 1 << second.left.start, all_right),))
    trans, capped, elapsed = _walk_context(
        S, C, A, start, state_cap=state_cap, time_cap=time_cap, right=False
    )
    complete = not capped
    return CascadeContextDFA(
        A,
        start,
        trans,
        tuple(range(len(S.relations))),
        tuple(S.relations),
        S.arena,
        False,
        complete,
        elapsed,
    )


def build_right_context(
    first: LazyBimachine,
    second: LazyBimachine,
    *,
    order: Sequence[int] = (2, 1, 0),
    state_cap: int | None = None,
    time_cap: float | None = None,
) -> CascadeContextDFA:
    if first.alphabet != second.alphabet:
        raise ValueError("alphabet mismatch")
    A = first.alphabet
    S = _RelationStates(
        (len(first.left.states), len(second.right.states), len(first.right.states)),
        order,
    )
    C = _Behavior(first, second)
    all_left = (1 << len(first.left.states)) - 1
    start = S.intern(((all_left, 1 << second.right.start, 1 << first.right.start),))
    trans, capped, elapsed = _walk_context(
        S, C, A, start, state_cap=state_cap, time_cap=time_cap, right=True
    )
    complete = not capped
    return CascadeContextDFA(
        A,
        start,
        trans,
        tuple(range(len(S.relations))),
        tuple(S.relations),
        S.arena,
        True,
        complete,
        elapsed,
    )


class _CascadeOutput:
    __slots__ = ("cache", "cache_enabled", "first", "left", "right", "second")

    def __init__(
        self,
        first: LazyBimachine,
        second: LazyBimachine,
        left: CascadeContextDFA,
        right: CascadeContextDFA,
        cache_enabled: bool = False,
    ) -> None:
        self.first = first
        self.second = second
        self.left = left
        self.right = right
        self.cache: dict[tuple[int, int, int], _Word | None] = {}
        self.cache_enabled = bool(cache_enabled)

    def __call__(self, ls: int, a: int, rs: int) -> tuple[int, ...] | None:
        key = (int(ls), int(a), int(rs))
        if self.cache_enabled and key in self.cache:
            return self.cache[key]
        # Find one compatible witness. Functional bimachine composition proves
        # every compatible witness has the same output; randomized/exhaustive
        # tests on small powers protect the implementation of the relation joins.
        for l1mask, l2mask, r_before_mask in self.left.boxes(ls):
            for l_after_mask, r2_after_mask, r_after_mask in self.right.boxes(rs):
                for r_after in _values(r_after_mask):
                    r_before = self.first.right.step(r_after, a)
                    if r_before is None or not ((r_before_mask >> r_before) & 1):
                        continue
                    for l1 in _values(l1mask):
                        l_after = self.first.left.step(l1, a)
                        if l_after is None or not ((l_after_mask >> l_after) & 1):
                            continue
                        v = self.first.emit(l1, a, r_after)
                        if v is None:
                            continue
                        for l2 in _values(l2mask):
                            for r2_after in _values(r2_after_mask):
                                w = _fragment(self.second, l2, v, r2_after)
                                if w is not None:
                                    if self.cache_enabled:
                                        self.cache[key] = w
                                    return w
        if self.cache_enabled:
            self.cache[key] = None
        return None


@dataclass(slots=True)
class CascadeComposition:
    machine: LazyBimachine | None
    left: CascadeContextDFA
    right: CascadeContextDFA

    @property
    def complete(self) -> bool:
        return self.left.complete and self.right.complete


def compose_bimachines_cascade(
    first: LazyBimachine,
    second: LazyBimachine,
    *,
    left_order: Sequence[int] = (0, 1, 2),
    right_order: Sequence[int] = (2, 1, 0),
    state_cap: int | None = None,
    time_cap: float | None = None,
    cache_outputs: bool = False,
) -> CascadeComposition:
    left = build_left_context(
        first, second, order=left_order, state_cap=state_cap, time_cap=time_cap
    )
    right = build_right_context(
        first, second, order=right_order, state_cap=state_cap, time_cap=time_cap
    )
    if not (left.complete and right.complete):
        return CascadeComposition(None, left, right)
    ldfa = DFA(first.alphabet, left.start, left.trans, left.states, False)
    rdfa = DFA(first.alphabet, right.start, right.trans, right.states, True)
    resolver = _CascadeOutput(first, second, left, right, cache_enabled=cache_outputs)
    return CascadeComposition(
        LazyBimachine(
            first.base,
            first.alphabet,
            ldfa,
            rdfa,
            resolver,
            cache_enabled=cache_outputs,
        ),
        left,
        right,
    )


__all__ = [
    "CascadeComposition",
    "CascadeContextDFA",
    "CascadeContextMetrics",
    "build_left_context",
    "build_right_context",
    "compose_bimachines_cascade",
]
