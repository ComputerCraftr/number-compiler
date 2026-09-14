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
from collections.abc import Hashable, Sequence
from dataclasses import dataclass
from typing import Literal

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
            nxt = set()
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
    h = tuple(half)
    full = h + (h[-2::-1] if parity else h[::-1])
    d = len(full)
    t = base - 1
    L = [0] * (d + 1)
    for i, s in enumerate(full):
        L[i + 1] = carry(s, L[i], t)
    R = [0] * (d + 1)
    for i in range(d - 1, -1, -1):
        R[i] = carry(full[i], R[i + 1], t)
    g = L[d]
    if not g:
        out = [
            2 * full[i] + L[i] + R[i + 1] - base * (L[i + 1] + R[i]) for i in range(d)
        ]
    else:
        out = [0] * (d + 1)
        out[0] = full[0] + 1 - base * L[1]
        out[d] = out[0]
        for i in range(1, d):
            out[i] = full[i] + full[i - 1] + L[i] + R[i] - base * (L[i + 1] + R[i - 1])
    p2 = len(out) & 1
    h2 = (len(out) + 1) // 2
    return p2, tuple(out[:h2])


def build(base: int = 10) -> FST:
    b = base
    t = b - 1
    vals = range(2 * b - 1)
    ids = {}
    sts: list[HalfState] = []

    def sid(x: HalfState) -> int:
        if x not in ids:
            ids[x] = len(sts)
            sts.append(x)
        return ids[x]

    # super initial state consumes parity tag.  After that:
    # ("B", p, g=R0, L_i, R_i, prev_s, L_before_prev, count_nonempty)
    S = sid(("S",))
    arcs: defaultdict[int, list[Arc]] = defaultdict(list)
    finals = {}
    dq = deque([S])
    seen = set()
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
                arcs[qi].append(Arc(s, y, ni))
                if ni not in seen:
                    dq.append(ni)
    return trim(FST(b, (S,), {q: tuple(v) for q, v in arcs.items()}, finals))


def trim(t: FST) -> FST:
    reach = set(t.initials)
    dq = deque(t.initials)
    while dq:
        q = dq.popleft()
        for a in t.arcs.get(q, ()):
            if a.dest not in reach:
                reach.add(a.dest)
                dq.append(a.dest)
    rev: defaultdict[int, list[int]] = defaultdict(list)
    for q, aa in t.arcs.items():
        for a in aa:
            rev[a.dest].append(q)
    live = set(t.finals)
    dq = deque(live)
    while dq:
        q = dq.popleft()
        for z in rev.get(q, ()):
            if z not in live:
                live.add(z)
                dq.append(z)
    keep = reach & live
    mp = {q: i for i, q in enumerate(sorted(keep))}
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
    part = {}
    cc: dict[Hashable, int] = {}
    for q in qs:
        k = t.finals.get(q, None)
        cc.setdefault(k, len(cc))
        part[q] = cc[k]
    while True:
        cc = {}
        new = {}
        for q in qs:
            sig = (
                t.finals.get(q, None),
                tuple(sorted((a.inp, a.out, part[a.dest]) for a in t.arcs.get(q, ()))),
            )
            cc.setdefault(sig, len(cc))
            new[q] = cc[sig]
        # This construction is a monotone partition refinement: signatures are
        # expressed through the previous partition, so classes can split but not
        # merge.  Equal class counts therefore mean the partition is stable.
        if len(set(new.values())) == len(set(part.values())):
            part = new
            break
        part = new
    reps: dict[int, int] = {}
    for q, c in part.items():
        reps.setdefault(c, q)
    cmap = {c: i for i, c in enumerate(sorted(reps))}
    arcs = {}
    fin = {}
    for c, q in reps.items():
        nq = cmap[c]
        items = {(a.inp, a.out, cmap[part[a.dest]]) for a in t.arcs.get(q, ())}
        arcs[nq] = tuple(Arc(*x) for x in sorted(items))
        if q in t.finals:
            fin[nq] = t.finals[q]
    ini = tuple(sorted({cmap[part[q]] for q in t.initials}))
    return trim(FST(t.base, ini, arcs, fin))


def compose(a: FST, b: FST) -> FST:
    pairid = {}
    pairs: list[tuple[int, int]] = []

    def sid(x: tuple[int, int]) -> int:
        if x not in pairid:
            pairid[x] = len(pairs)
            pairs.append(x)
        return pairid[x]

    ini = tuple(sid((p, q)) for p in a.initials for q in b.initials)
    arcs: defaultdict[int, list[Arc]] = defaultdict(list)
    fin = {}
    dq = deque(ini)
    seen = set()
    idx: dict[int, dict[int, list[Arc]]] = {q: defaultdict(list) for q in b.arcs}
    for q, aa in b.arcs.items():
        for z in aa:
            idx[q][z.inp].append(z)
    while dq:
        qi = dq.popleft()
        if qi in seen:
            continue
        seen.add(qi)
        p, q = pairs[qi]
        for x in a.arcs.get(p, ()):
            for y in idx.get(q, {}).get(x.out, ()):
                ni = sid((x.dest, y.dest))
                arcs[qi].append(Arc(x.inp, y.out, ni))
                if ni not in seen:
                    dq.append(ni)
        if p in a.finals:
            front: set[tuple[int, tuple[int, ...]]] = {(q, ())}
            for sym in a.finals[p]:
                nf = set()
                for qq, o in front:
                    for y in idx.get(qq, {}).get(sym, ()):
                        nf.add((y.dest, o + (y.out,)))
                front = nf
            outs = {o + b.finals[qq] for qq, o in front if qq in b.finals}
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
        h = [rng.randrange(19) for _ in range(rng.randrange(1, 7))]
        h[0] = h[0] or 1
        exp = reference_half(p, h)
        got = T.apply((P(p, 10),) + tuple(h))
        dec = (got[0] - (2 * 10 - 1), got[1:])
        assert dec == exp, (p, h, dec, exp)
    Q = T
    for e in range(1, 5):
        st = time.perf_counter()
        Q = compose(Q, Q)
        dt = time.perf_counter() - st
        print("pow", 2**e, Q.states, Q.arc_count, len(Q.finals), "sec", dt, flush=True)
        for _ in range(50):
            p = rng.randrange(2)
            h = [rng.randrange(19) for _ in range(rng.randrange(1, 5))]
            h[0] = h[0] or 1
            pp, hh = p, tuple(h)
            for __ in range(2**e):
                pp, hh = reference_half(pp, hh)
            got = Q.apply((P(p, 10),) + tuple(h))
            dec = (got[0] - (2 * 10 - 1), got[1:])
            assert dec == (pp, hh)


if __name__ == "__main__":
    selftest()
