"""Direct dependency-cascade determinization for bimachine composition.

Unlike the classical construction, a determinized context state is never stored
as a frozenset of triples.  It is a canonical dependency map

    middle_state -> downstream_state -> bitset(upstream_states)

which is exactly the cascade ordering that gave the best T2 compression.  The
transition performs the relational join at each dependency level and interns the
result directly.
"""

from __future__ import annotations

import json
import random
import time
from collections import defaultdict, deque
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TypeVar

from devtools.paths import report_output
from devtools.verification.builders.bimachine_lazy_power import (
    LazyBimachine,
    compose,
    lazy_from_eager,
)
from devtools.verification.builders.bimachine_power import (
    build_step,
    encode,
    predecessor_index,
    scan_word,
)
from devtools.verification.random_inputs import random_half

Relation = tuple[tuple[int, tuple[tuple[int, int], ...]], ...]
_CacheKey = TypeVar("_CacheKey")
_CacheValue = TypeVar("_CacheValue")


def _memoized(
    cache: dict[_CacheKey, _CacheValue],
    key: _CacheKey,
    produce: Callable[[], _CacheValue],
) -> _CacheValue:
    if key not in cache:
        cache[key] = produce()
    return cache[key]


def _compose_caches() -> tuple[
    dict[tuple[int, int, int], tuple[int, ...] | None],
    dict[tuple[int, tuple[int, ...]], int | None],
    dict[tuple[int, int, int], tuple[tuple[tuple[int, ...], int], ...]],
]:
    return {}, {}, {}


def _cached_emit(
    machine: LazyBimachine,
    cache: dict[tuple[int, int, int], tuple[int, ...] | None],
) -> Callable[[int, int, int], tuple[int, ...] | None]:
    def emit(left_state: int, symbol: int, right_state: int) -> tuple[int, ...] | None:
        return _memoized(
            cache,
            (left_state, symbol, right_state),
            lambda: machine.emit(left_state, symbol, right_state),
        )

    return emit


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def bits(mask: int) -> Iterator[int]:
    while mask:
        lsb = mask & -mask
        yield lsb.bit_length() - 1
        mask -= lsb


@dataclass
class DepDFA:
    alphabet: tuple[int, ...]
    start: int
    trans: dict[tuple[int, int], int]
    states: tuple[int, ...]
    data: dict[int, Relation]
    right: bool = False

    def step(self, q: int, a: int) -> int | None:
        return self.trans.get((q, a))

    def word(self, q: int | None, w: Sequence[int]) -> int | None:
        return scan_word(q, w, self.right, self.step)


class RelationInterner:
    __slots__ = ("bit_count", "edge_count", "ids", "states")

    def __init__(self) -> None:
        self.states: list[Relation] = []
        self.ids: dict[Relation, int] = {}
        self.edge_count = 0
        self.bit_count = 0

    @staticmethod
    def freeze(
        d: Mapping[int, Mapping[int, int]],
    ) -> tuple[tuple[int, tuple[tuple[int, int], ...]], ...]:
        # d: outer -> inner -> bitset
        return tuple(
            (int(o), tuple((int(i), int(m)) for i, m in sorted(inner.items()) if m))
            for o, inner in sorted(d.items())
            if any(inner.values())
        )

    def intern(self, d: Mapping[int, Mapping[int, int]]) -> int:
        key = self.freeze(d)
        old = self.ids.get(key)
        if old is not None:
            return old
        q = len(self.states)
        self.ids[key] = q
        self.states.append(key)
        self.edge_count += sum(len(inner) for _, inner in key)
        self.bit_count += sum(
            int(mask).bit_count() for _, inner in key for _, mask in inner
        )
        return q

    def thaw(self, q: int) -> Relation:
        return self.states[q]


def build_left(
    B1: LazyBimachine, B2: LazyBimachine, cap: int = 100_000
) -> tuple[DepDFA, RelationInterner, bool, float]:
    A = B1.alphabet
    R = RelationInterner()
    # relation order: r1 -> l2 -> bitset(l1)
    startd0 = {r: {B2.left.start: 1 << B1.left.start} for r in B1.right.states}
    start = R.intern(startd0)
    predR = predecessor_index(B1.right.states, A, B1.right.step)
    trans = {}
    dq = deque([start])
    seen = set()
    emit_cache, word_cache, mask_map_cache = _compose_caches()

    emit = _cached_emit(B1, emit_cache)

    def word(left_state: int, w: Sequence[int]) -> int | None:
        return _memoized(
            word_cache,
            (left_state, tuple(w)),
            lambda: B2.left.word(left_state, w),
        )

    def map_mask(a: int, r2: int, mask: int) -> tuple[tuple[tuple[int, ...], int], ...]:
        # Group a whole set of l1 states by the emitted intermediate word.
        # The resulting bitset is already in B1's next-left-state coordinate.
        k = (a, r2, mask)
        z = mask_map_cache.get(k)
        if z is not None:
            return z
        groups: defaultdict[tuple[int, ...], int] = defaultdict(int)
        for l1 in bits(mask):
            l1n = B1.left.step(l1, a)
            if l1n is None:
                continue
            v = emit(l1, a, r2)
            if v is None:
                continue
            groups[v] |= 1 << l1n
        z = tuple(groups.items())
        mask_map_cache[k] = z
        return z

    t0 = time.perf_counter()
    capped = False
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        state = R.thaw(q)
        for a in A:
            out: defaultdict[int, defaultdict[int, int]] = defaultdict(
                lambda: defaultdict(int)
            )
            for r1, inner in state:
                for r2 in predR[a].get(r1, ()):
                    for l2, mask in inner:
                        for v, nextmask in map_mask(a, r2, mask):
                            l2n = word(l2, v)
                            if l2n is not None:
                                out[r2][l2n] |= nextmask
            if not out:
                continue
            z = R.intern(out)
            trans[q, a] = z
            if z not in seen:
                if len(R.states) >= cap:
                    capped = True
                    return (
                        DepDFA(
                            A,
                            start,
                            trans,
                            tuple(range(len(R.states))),
                            {i: R.states[i] for i in range(len(R.states))},
                        ),
                        R,
                        capped,
                        time.perf_counter() - t0,
                    )
                dq.append(z)
    return (
        DepDFA(
            A,
            start,
            trans,
            tuple(range(len(R.states))),
            {i: R.states[i] for i in range(len(R.states))},
        ),
        R,
        capped,
        time.perf_counter() - t0,
    )


def build_right(
    B1: LazyBimachine, B2: LazyBimachine, cap: int = 100_000
) -> tuple[DepDFA, RelationInterner, bool, float]:
    A = B1.alphabet
    R = RelationInterner()
    # relation order: r2 -> rr2 -> bitset(l2) for NFA triple (l2,r2,rr2)
    startd = {
        B1.right.start: {
            B2.right.start: sum(1 << left_state for left_state in B1.left.states)
        }
    }
    start = R.intern(startd)
    predL = predecessor_index(B1.left.states, A, B1.left.step)
    trans = {}
    dq = deque([start])
    seen = set()
    emit_cache, word_cache, mask_map_cache = _compose_caches()

    emit = _cached_emit(B1, emit_cache)

    def word(r: int, w: Sequence[int]) -> int | None:
        return _memoized(
            word_cache,
            (r, tuple(w)),
            lambda: B2.right.word(r, w),
        )

    def map_mask(
        a: int, r2: int, mask_l2: int
    ) -> tuple[tuple[tuple[int, ...], int], ...]:
        # Invert B1.left on the whole l2-set and group predecessor l1 states
        # by the emitted word; independent of B2's right context.
        k = (a, r2, mask_l2)
        z = mask_map_cache.get(k)
        if z is not None:
            return z
        groups: defaultdict[tuple[int, ...], int] = defaultdict(int)
        for l2 in bits(mask_l2):
            for l1 in predL[a].get(l2, ()):
                v = emit(l1, a, r2)
                if v is not None:
                    groups[v] |= 1 << l1
        z = tuple(groups.items())
        mask_map_cache[k] = z
        return z

    t0 = time.perf_counter()
    capped = False
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        state = R.thaw(q)
        for a in A:
            out: defaultdict[int, defaultdict[int, int]] = defaultdict(
                lambda: defaultdict(int)
            )
            for r2, inner in state:
                r1 = B1.right.step(r2, a)
                if r1 is None:
                    continue
                for rr2, mask_l2 in inner:
                    for v, mask_l1 in map_mask(a, r2, mask_l2):
                        rr1 = word(rr2, v)
                        if rr1 is not None:
                            out[r1][rr1] |= mask_l1
            if not out:
                continue
            z = R.intern(out)
            trans[q, a] = z
            if z not in seen:
                if len(R.states) >= cap:
                    capped = True
                    return (
                        DepDFA(
                            A,
                            start,
                            trans,
                            tuple(range(len(R.states))),
                            {i: R.states[i] for i in range(len(R.states))},
                            right=True,
                        ),
                        R,
                        capped,
                        time.perf_counter() - t0,
                    )
                dq.append(z)
    return (
        DepDFA(
            A,
            start,
            trans,
            tuple(range(len(R.states))),
            {i: R.states[i] for i in range(len(R.states))},
            right=True,
        ),
        R,
        capped,
        time.perf_counter() - t0,
    )


def main() -> None:
    B = lazy_from_eager(build_step(10))
    T2 = compose(B, B, verbose=False)
    metrics: dict[str, dict[str, int | float]] = {
        "T2_flat": {"left": len(T2.left.states), "right": len(T2.right.states)}
    }
    # Rebuild T2 determinization via cascades; state counts must match classical.
    L2, Li2, capL2, secL2 = build_left(B, B, cap=5000)
    R2, Ri2, capR2, secR2 = build_right(B, B, cap=5000)
    metrics["T2_cascade"] = {
        "left_states": len(L2.states),
        "right_states": len(R2.states),
        "left_edges": Li2.edge_count,
        "right_edges": Ri2.edge_count,
        "left_members": Li2.bit_count,
        "right_members": Ri2.bit_count,
        "left_seconds": secL2,
        "right_seconds": secR2,
        "capped": capL2 or capR2,
    }
    assert len(L2.states) == len(T2.left.states), (len(L2.states), len(T2.left.states))
    assert len(R2.states) == len(T2.right.states), (
        len(R2.states),
        len(T2.right.states),
    )
    # Need the exact T2 output resolver from the verified lazy composition, but
    # replace only its context automata by equivalent cascade DFAs for T4 context exploration.
    T2c = LazyBimachine(T2.base, T2.alphabet, L2, R2, T2.resolver, {})
    # NOTE: resolver expects flat T2 state ids; cascade DFA ids are canonically generated
    # in the same BFS order only for this T2 construction. Validate that before use.
    rng = random.Random(196)
    for _ in range(100):
        p = rng.randrange(2)
        h = random_half(rng, 4)
        assert T2c.output(encode(p, h, 10)) == T2.output(encode(p, h, 10))
    # T4 direct dependency-cascade determinization.  Cap remains a diagnostic,
    # but no local triple universe is ever materialized.
    L4, Li4, capL4, secL4 = build_left(T2c, T2c, cap=250)
    R4, Ri4, capR4, secR4 = build_right(T2c, T2c, cap=250)
    metrics["T4_cascade"] = {
        "left_states": len(L4.states),
        "right_states": len(R4.states),
        "left_edges": Li4.edge_count,
        "right_edges": Ri4.edge_count,
        "left_members": Li4.bit_count,
        "right_members": Ri4.bit_count,
        "left_seconds": secL4,
        "right_seconds": secR4,
        "left_capped": capL4,
        "right_capped": capR4,
    }
    (
        report_output(
            "devtools.verification.builders.cascade_bimachine_power",
            "cascade_bimachine_metrics.json",
        )
    ).write_text(json.dumps(metrics, indent=2))
    (
        report_output(
            "devtools.verification.builders.cascade_bimachine_power",
            "CASCADE_BIMACHINE_RESULTS.md",
        )
    ).write_text(
        f"""# Direct dependency-cascade bimachine powering\n\nThe determinized context state itself is represented as a hierarchical dependency function rather than a flat subset of Cartesian triples.\n\n## T2 exact cross-check\n\n- classical: {len(T2.left.states)} left / {len(T2.right.states)} right states\n- cascade: {len(L2.states)} left / {len(R2.states)} right states\n- cascade dependency edges: {Li2.edge_count:,} left / {Ri2.edge_count:,} right\n- represented triple members: {Li2.bit_count:,} left / {Ri2.bit_count:,} right\n\nThe cascade T2 automata reproduce the classical state counts and were checked on random encoded pair halves.\n\n## T4 cascade probe\n\n- left states: {len(L4.states):,}, dependency edges {Li4.edge_count:,}, capped={capL4}\n- right states: {len(R4.states):,}, dependency edges {Ri4.edge_count:,}, capped={capR4}\n- build times: {secL4:.3f}s left / {secR4:.3f}s right\n\nThis construction never materializes the local NFA triple universe.  If it still reaches the state cap, the remaining growth is in distinct dependency functions rather than flat tuple storage.\n"""
    )
    print(json.dumps(metrics, indent=2))


if __name__ == "__main__":
    main()
