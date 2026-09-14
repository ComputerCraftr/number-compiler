"""Experimental exact real-time functional transducer for pair-field successor.

This is research-only.  It represents the one-step map as an unambiguous
finite-state transducer with one output symbol per consumed input symbol and a
short final-output suffix.  Such transducers compose directly without any
width-sized Boolean lowering.  A conservative strong-bisimulation quotient is
applied after composition.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Hashable, Sequence
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class Arc:
    inp: int
    out: int
    dest: int


@dataclass
class RTTransducer:
    base: int
    initials: tuple[int, ...]
    arcs: dict[int, tuple[Arc, ...]]
    finals: dict[int, tuple[int, ...]]

    @property
    def states(self) -> int:
        return len(set(self.arcs) | set(self.finals) | set(self.initials))

    @property
    def arc_count(self) -> int:
        return sum(map(len, self.arcs.values()))

    def apply(self, word: Sequence[int]) -> tuple[int, ...]:
        # Keep distinct (state, output) paths.  The machine is functional and
        # unambiguous on complete accepted inputs, so exactly one result remains.
        cur: dict[tuple[int, tuple[int, ...]], None] = {
            (q, ()): None for q in self.initials
        }
        for x in map(int, word):
            nxt: dict[tuple[int, tuple[int, ...]], None] = {}
            for q, out in cur:
                for a in self.arcs.get(q, ()):
                    if a.inp == x:
                        nxt[(a.dest, out + (a.out,))] = None
            cur = nxt
            if not cur:
                raise ValueError("input rejected")
        results = set()
        for q, out in cur:
            if q in self.finals:
                results.add(out + self.finals[q])
        if len(results) != 1:
            raise AssertionError(f"expected one functional output, got {len(results)}")
        return next(iter(results))


def carry_step(s: int, c: int, threshold: int) -> int:
    return 0 if s < threshold else (c if s == threshold else 1)


def reference_step(word: Sequence[int], base: int = 10) -> tuple[int, ...]:
    w = tuple(map(int, word))
    d = len(w)
    t = base - 1
    L = [0] * (d + 1)
    for i, s in enumerate(w):
        L[i + 1] = carry_step(s, L[i], t)
    R = [0] * (d + 1)
    for i in range(d - 1, -1, -1):
        R[i] = carry_step(w[i], R[i + 1], t)
    g = L[d]
    if not g:
        return tuple(
            2 * w[i] + L[i] + R[i + 1] - base * (L[i + 1] + R[i]) for i in range(d)
        )
    out = [0] * (d + 1)
    out[0] = w[0] + 1 - base * L[1]
    out[d] = out[0]
    for i in range(1, d):
        out[i] = w[i] + w[i - 1] + L[i] + R[i] - base * (L[i + 1] + R[i - 1])
    return tuple(out)


def build_step(base: int = 10) -> RTTransducer:
    b = int(base)
    t = b - 1
    alphabet = range(2 * b - 1)
    # State tuples:
    #   start/ordinary no-growth: ("N", L, R, g=0)
    #   growth start/ordinary:    ("G", L, R, prev_symbol_or_-1, edge_or_-1)
    # Global g is encoded by mode.  R is the guessed right-boundary carry R_i.
    state_id: dict[tuple[str, int, int, int, int], int] = {}
    states: list[tuple[str, int, int, int, int]] = []

    def sid(s: tuple[str, int, int, int, int]) -> int:
        if s not in state_id:
            state_id[s] = len(states)
            states.append(s)
        return state_id[s]

    initials = []
    for g in (0, 1):
        for R0 in (0, 1):
            initials.append(sid(("G" if g else "N", 0, R0, -1, -1)))

    arcs = defaultdict(list)
    finals: dict[int, tuple[int, ...]] = {}
    q = deque(initials)
    seen = set()
    while q:
        qi = q.popleft()
        if qi in seen:
            continue
        seen.add(qi)
        st = states[qi]
        mode, L, R, prev, edge = st
        g = int(mode == "G")
        # Accept after at least one symbol only: prev=-1 is start state.
        if prev != -1 and R == 0 and L == g:
            finals[qi] = () if not g else (edge,)
        for s in alphabet:
            L1 = carry_step(s, L, t)
            # Choose R_(i+1) such that current R_i is consistent.
            for R1 in (0, 1):
                if carry_step(s, R1, t) != R:
                    continue
                if not g:
                    y = 2 * s + L + R1 - b * (L1 + R)
                    ns = ("N", L1, R1, 0, -1)  # prev marker 0 means nonempty
                else:
                    if prev == -1:
                        y = s + 1 - b * L1
                        e = y
                    else:
                        Rprev = carry_step(prev, R, t)
                        y = s + prev + L + R - b * (L1 + Rprev)
                        e = edge
                    ns = ("G", L1, R1, s, e)
                if not 0 <= y <= 2 * (b - 1):
                    # Inconsistent branch guesses can produce out-of-range values;
                    # they cannot represent a valid reverse/add state path.
                    continue
                ni = sid(ns)
                arcs[qi].append(Arc(s, y, ni))
                if ni not in seen:
                    q.append(ni)
    return trim(
        RTTransducer(b, tuple(initials), {k: tuple(v) for k, v in arcs.items()}, finals)
    )


def trim(t: RTTransducer) -> RTTransducer:
    reachable = set(t.initials)
    dq = deque(t.initials)
    while dq:
        q = dq.popleft()
        for a in t.arcs.get(q, ()):
            if a.dest not in reachable:
                reachable.add(a.dest)
                dq.append(a.dest)
    rev = defaultdict(list)
    for q, aa in t.arcs.items():
        for a in aa:
            rev[a.dest].append(q)
    live = set(t.finals)
    dq = deque(t.finals)
    while dq:
        q = dq.popleft()
        for p in rev.get(q, ()):
            if p not in live:
                live.add(p)
                dq.append(p)
    keep = reachable & live
    ids = {q: i for i, q in enumerate(sorted(keep))}
    arcs = {
        ids[q]: tuple(Arc(a.inp, a.out, ids[a.dest]) for a in aa if a.dest in keep)
        for q, aa in t.arcs.items()
        if q in keep
    }
    finals = {ids[q]: o for q, o in t.finals.items() if q in keep}
    initials = tuple(ids[q] for q in t.initials if q in keep)
    return RTTransducer(t.base, initials, arcs, finals)


def compose(a: RTTransducer, b: RTTransducer) -> RTTransducer:
    if a.base != b.base:
        raise ValueError("base mismatch")
    pair_id: dict[tuple[int, int], int] = {}
    pairs: list[tuple[int, int]] = []

    def sid(pair: tuple[int, int]) -> int:
        if pair not in pair_id:
            pair_id[pair] = len(pairs)
            pairs.append(pair)
        return pair_id[pair]

    initials = tuple(sid((p, q)) for p in a.initials for q in b.initials)
    arcs = defaultdict(list)
    finals: dict[int, tuple[int, ...]] = {}
    dq = deque(initials)
    seen = set()
    # Index second arcs by input symbol.
    idx: dict[int, dict[int, list[Arc]]] = {q: defaultdict(list) for q in b.arcs}
    for q, aa in b.arcs.items():
        for x in aa:
            idx[q][x.inp].append(x)
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
        # Feed a's final output suffix through b and then use b's final output.
        if p in a.finals:
            frontier: set[tuple[int, tuple[int, ...]]] = {(q, ())}
            for sym in a.finals[p]:
                nf = set()
                for qq, out in frontier:
                    for y in idx.get(qq, {}).get(sym, ()):
                        nf.add((y.dest, out + (y.out,)))
                frontier = nf
            outs = set()
            for qq, out in frontier:
                if qq in b.finals:
                    outs.add(out + b.finals[qq])
            if len(outs) > 1:
                raise AssertionError("composition lost functionality")
            if outs:
                finals[qi] = next(iter(outs))
    return bisim_minimize(
        trim(
            RTTransducer(
                a.base, initials, {k: tuple(v) for k, v in arcs.items()}, finals
            )
        )
    )


def bisim_minimize(t: RTTransducer) -> RTTransducer:
    states = sorted(set(t.arcs) | set(t.finals) | set(t.initials))
    # Initial partition by final-output word (None for nonfinal).
    keys = {q: (t.finals.get(q, None),) for q in states}
    part = {}
    classes: dict[Hashable, int] = {}
    for q in states:
        k = keys[q]
        classes.setdefault(k, len(classes))
        part[q] = classes[k]
    while True:
        classes = {}
        new = {}
        for q in states:
            sig = (
                t.finals.get(q, None),
                tuple(sorted((a.inp, a.out, part[a.dest]) for a in t.arcs.get(q, ()))),
            )
            classes.setdefault(sig, len(classes))
            new[q] = classes[sig]
        if all(new[q] == part[q] for q in states):
            break
        part = new
    reps: dict[int, int] = {}
    for q, c in part.items():
        reps.setdefault(c, q)
    remap = {c: i for i, c in enumerate(sorted(reps))}
    arcs = {}
    finals: dict[int, tuple[int, ...]] = {}
    for c, q in reps.items():
        nq = remap[c]
        aa = {(a.inp, a.out, remap[part[a.dest]]) for a in t.arcs.get(q, ())}
        arcs[nq] = tuple(Arc(*x) for x in sorted(aa))
        if q in t.finals:
            finals[nq] = t.finals[q]
    initials = tuple(sorted({remap[part[q]] for q in t.initials}))
    return trim(RTTransducer(t.base, initials, arcs, finals))


def palindrome_from_half(half: list[int], odd: bool = True) -> tuple[int, ...]:
    h = tuple(half)
    return h + (h[-2::-1] if odd else h[::-1])


def selftest() -> None:
    import random
    import time

    T = build_step(10)
    print(
        "T", T.states, T.arc_count, "initials", len(T.initials), "finals", len(T.finals)
    )
    rng = random.Random(196)
    for _ in range(100):
        h = [rng.randrange(19) for _ in range(rng.randrange(1, 6))]
        h[0] = h[0] or 1
        w = palindrome_from_half(h, bool(rng.randrange(2)))
        got = T.apply(w)
        exp = reference_step(w)
        assert got == exp, (w, got, exp)
    P = T
    for k in range(1, 5):
        t0 = time.perf_counter()
        P = compose(P, P)
        dt = time.perf_counter() - t0
        print(
            "power",
            2**k,
            "states",
            P.states,
            "arcs",
            P.arc_count,
            "initials",
            len(P.initials),
            "finals",
            len(P.finals),
            "sec",
            dt,
        )
        for _ in range(20):
            h = [rng.randrange(19) for _ in range(rng.randrange(1, 5))]
            h[0] = h[0] or 1
            w = palindrome_from_half(h, bool(rng.randrange(2)))
            exp = w
            for __ in range(2**k):
                exp = reference_step(exp)
            assert P.apply(w) == exp


if __name__ == "__main__":
    selftest()
