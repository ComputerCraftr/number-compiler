"""Exact tagged pair-half transducer and direct power experiment.

Input word:  (PARITY_TAG, s0, ..., s_(h-1))
Output word: (target parity tag, target independent half...)

The full pair palindrome is implicit.  Right-carry lookahead is guessed and
verified at the center boundary, yielding an unambiguous functional real-time
transducer with a much smaller state space than the full-word experiment.
"""

from __future__ import annotations

import random
import time
from collections import defaultdict, deque
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Literal

from devtools.verification.partition_refinement import (
    partition_representatives,
    stable_partition,
)
from devtools.verification.random_inputs import random_half
from devtools.verification.reverse_pair_reference import reference_pair_half
from devtools.verification.transducer_graph import (
    DenseInterner,
    append_reachable_edge,
    compose_product_graph,
    compose_suffix_outputs,
    quotient_graph,
    trim_ids,
)

# parity tags live above the pair alphabet
HalfState = tuple[Literal["S"]] | tuple[Literal["B"], int, int, int, int, int, int, int]


def P(p: int, base: int) -> int:
    return 2 * base - 1 + int(p)


def carry(s: int, c: int, t: int) -> int:
    return 0 if s < t else (c if s == t else 1)


@dataclass(frozen=True, slots=True)
class Arc:
    inp: int
    out: int
    dest: int


@dataclass
class FST:
    base: int
    initials: tuple[int, ...]
    arcs: dict[int, tuple[Arc, ...]]
    finals: dict[int, tuple[int, ...]]

    @property
    def states(self) -> int:
        return len(set(self.arcs) | set(self.finals) | set(self.initials))

    @property
    def arc_count(self) -> int:
        return sum(len(x) for x in self.arcs.values())

    def apply(self, word: Sequence[int]) -> tuple[int, ...]:
        cur: set[tuple[int, tuple[int, ...]]] = {(q, ()) for q in self.initials}
        for x in word:
            nxt: set[tuple[int, tuple[int, ...]]] = set()
            for q, o in cur:
                for a in self.arcs.get(q, ()):
                    if a.inp == x:
                        nxt.add((a.dest, o + (a.out,)))
            cur = nxt
        outs = {o + self.finals[q] for q, o in cur if q in self.finals}
        if len(outs) != 1:
            raise AssertionError(("functional", len(outs), word))
        return next(iter(outs))


def reference_half(
    parity: int, half: Sequence[int], base: int = 10
) -> tuple[int, tuple[int, ...]]:
    return reference_pair_half(parity, half, base, carry)


def build(base: int = 10) -> FST:
    b = base
    t = b - 1
    vals = range(2 * b - 1)
    state_interner: DenseInterner[HalfState] = DenseInterner()
    sts = state_interner.values
    sid = state_interner.intern

    # super initial state consumes parity tag.  After that:
    # ("B", p, g=R0, L_i, R_i, prev_s, L_before_prev, count_nonempty)
    S = sid(("S",))
    arcs: defaultdict[int, list[Arc]] = defaultdict(list)
    finals: dict[int, tuple[int, ...]] = {}
    dq = deque([S])
    seen: set[int] = set()
    while dq:
        qi = dq.popleft()
        if qi in seen:
            continue
        seen.add(qi)
        st = sts[qi]
        if st[0] == "S":
            for p in (0, 1):
                for g in (0, 1):
                    ns: HalfState = ("B", p, g, 0, g, -1, 0, 0)
                    ni = sid(ns)
                    arcs[qi].append(Arc(P(p, b), P(p ^ g, b), ni))
                    dq.append(ni)
            continue
        _, p, g, L, R, prev, Lbeforeprev, count = st
        # center boundary verifies the guessed right-carry path. Empty half invalid.
        if count:
            ok = (R == L) if p == 0 else (R == Lbeforeprev)
            if ok:
                suffix: tuple[int, ...] = ()
                if p == 0 and g == 1:
                    # even source -> odd target: emit the new center pair coefficient.
                    s = prev
                    Lh = L
                    Rh = R
                    Lhp1 = carry(s, Lh, t)
                    Rhm1 = carry(s, Rh, t)
                    center = 2 * s + Lh + Rh - b * (Lhp1 + Rhm1)
                    if 0 <= center <= 2 * (b - 1):
                        suffix = (center,)
                    else:
                        ok = False
                if ok:
                    finals[qi] = suffix
        for s in vals:
            L1 = carry(s, L, t)
            for R1 in (0, 1):
                if carry(s, R1, t) != R:
                    continue
                if g == 0:
                    y = 2 * s + L + R1 - b * (L1 + R)
                else:
                    if not count:
                        y = s + 1 - b * L1
                    else:
                        Rprev = carry(prev, R, t)
                        y = s + prev + L + R - b * (L1 + Rprev)
                if not 0 <= y <= 2 * (b - 1):
                    continue
                ns = ("B", p, g, L1, R1, s, L, 1)
                ni = sid(ns)
                append_reachable_edge(arcs, qi, Arc(s, y, ni), ni, seen, dq)
    return trim(FST(b, (S,), {q: tuple(v) for q, v in arcs.items()}, finals))


def trim(t: FST) -> FST:
    mp = trim_ids(t.initials, t.arcs, t.finals)
    keep = set(mp)
    return FST(
        t.base,
        tuple(mp[q] for q in t.initials if q in keep),
        {
            mp[q]: tuple(Arc(a.inp, a.out, mp[a.dest]) for a in aa if a.dest in keep)
            for q, aa in t.arcs.items()
            if q in keep
        },
        {mp[q]: v for q, v in t.finals.items() if q in keep},
    )


def bisim(t: FST) -> FST:
    qs = sorted(set(t.arcs) | set(t.finals) | set(t.initials))
    part = stable_partition(
        qs,
        lambda q: t.finals.get(q, None),
        lambda q, previous: (
            t.finals.get(q, None),
            tuple(sorted((a.inp, a.out, previous[a.dest]) for a in t.arcs.get(q, ()))),
        ),
    )
    reps, cmap = partition_representatives(part)
    arcs, fin, ini = quotient_graph(
        part,
        reps,
        cmap,
        t.arcs,
        t.finals,
        t.initials,
        lambda inp, out, dest: Arc(inp, out, dest),
    )
    return trim(FST(t.base, ini, arcs, fin))


def compose(a: FST, b: FST) -> FST:
    pairs, ini, idx, arcs = compose_product_graph(
        a.initials, b.initials, a.arcs, b.arcs, lambda edge: Arc(*edge)
    )
    fin: dict[int, tuple[int, ...]] = {}
    for qi, (p, q) in enumerate(pairs):
        if p in a.finals:
            outs = compose_suffix_outputs(q, a.finals[p], idx, b.finals)
            if len(outs) > 1:
                raise AssertionError("nonfunctional")
            if outs:
                fin[qi] = next(iter(outs))
    return bisim(trim(FST(a.base, ini, {q: tuple(v) for q, v in arcs.items()}, fin)))


def selftest() -> None:
    T = build()
    print("T", T.states, T.arc_count, len(T.finals), flush=True)
    rng = random.Random(196)
    for _ in range(500):
        p = rng.randrange(2)
        h = random_half(rng, 6)
        exp = reference_half(p, h)
        got = T.apply((P(p, 10),) + tuple(h))
        dec = (got[0] - (2 * 10 - 1), got[1:])
        assert dec == exp, (p, h, dec, exp)
    powered = T
    for e in range(1, 5):
        st = time.perf_counter()
        powered = compose(powered, powered)
        dt = time.perf_counter() - st
        print(
            "pow",
            2**e,
            powered.states,
            powered.arc_count,
            len(powered.finals),
            "sec",
            dt,
            flush=True,
        )
        for _ in range(50):
            p = rng.randrange(2)
            h = random_half(rng, 4)
            pp, hh = p, tuple(h)
            for __ in range(2**e):
                pp, hh = reference_half(pp, hh)
            got = powered.apply((P(p, 10),) + tuple(h))
            dec = (got[0] - (2 * 10 - 1), got[1:])
            assert dec == (pp, hh)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(selftest))
