"""Direct classical-bimachine powering experiment for reverse/add pair halves.

Implements the direct composition construction of Mihov/Schulz §6.4 for a
small exact pair-half bimachine.  Research-only until state-growth measurements
justify promotion into the guarded full-J backend.
"""

from __future__ import annotations

import random
import time
from collections import deque
from collections.abc import Callable, Hashable, Iterable, Mapping, Sequence
from collections.abc import Set as AbstractSet
from dataclasses import dataclass
from typing import Generic, Literal, TypeVar

from number_compiler.arithmetic.carry.carry_labels import (
    IDENTITY as I,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ONE as R1,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ZERO as R0,
)

State_co = TypeVar("State_co", covariant=True)

LeftState = tuple[Literal["S", "D"]] | tuple[Literal["V"], int, int, int, int]

RightState = tuple[Literal["S", "D"]] | tuple[Literal["A"], int, int, int]


def lab(s: int, b: int) -> int:
    t = b - 1
    return R0 if s < t else (I if s == t else R1)


def carry_label(m: int) -> int:
    return int(m == R1)


def compose_label(a: int, b: int) -> int:
    return b if b != I else a


def ptag(p: int, b: int) -> int:
    return 2 * b - 1 + p


def endtag(b: int) -> int:
    return 2 * b + 1


def first_nonI(*xs: int) -> int:
    for x in xs:
        if x != I:
            return x
    return I


@dataclass
class DFA(Generic[State_co]):
    alphabet: tuple[int, ...]
    start: int
    trans: dict[tuple[int, int], int]
    states: tuple[int, ...]
    data: Mapping[int, State_co]
    right: bool = False

    def step(self, q: int, a: int) -> int | None:
        return self.trans.get((q, a))

    def word(self, q: int | None, w: Sequence[int]) -> int | None:
        seq = reversed(tuple(w)) if self.right else w
        for a in seq:
            if q is None:
                return None
            q = self.step(q, a)
            if q is None:
                return None
        return q


@dataclass
class Bimachine:
    base: int
    alphabet: tuple[int, ...]
    left: DFA[object]
    right: DFA[object]
    out: dict[tuple[int, int, int], tuple[int, ...]]

    def output(self, word: Sequence[int]) -> tuple[int, ...]:
        w = tuple(word)
        n = len(w)
        ls = [self.left.start]
        for a in w:
            q = self.left.step(ls[-1], a)
            if q is None:
                raise ValueError(("left reject", a, ls[-1]))
            ls.append(q)
        rs = [0] * (n + 1)
        rs[n] = self.right.start
        for i in range(n - 1, -1, -1):
            q = self.right.step(rs[i + 1], w[i])
            if q is None:
                raise ValueError(("right reject", w[i], rs[i + 1]))
            rs[i] = q
        z: list[int] = []
        for i, a in enumerate(w):
            o = self.out.get((ls[i], a, rs[i + 1]))
            if o is None:
                raise ValueError(
                    (
                        "undefined output",
                        self.left.data[ls[i]],
                        a,
                        self.right.data[rs[i + 1]],
                    )
                )
            z.extend(o)
        return tuple(z)


def build_step(base: int = 10) -> Bimachine:
    b = base
    vals = tuple(range(2 * b - 1))
    P0, P1 = ptag(0, b), ptag(1, b)
    E = endtag(b)
    alphabet = vals + (P0, P1, E)
    # LEFT DFA. data: ('S',) ; ('V',p,first,last,prev) ; ('D',)
    ldata: list[LeftState] = []
    lid = {}
    lt = {}

    def L(x: LeftState) -> int:
        if x not in lid:
            lid[x] = len(ldata)
            ldata.append(x)
        return lid[x]

    sL = L(("S",))
    done = L(("D",))
    dq = deque([sL])
    seen = set()
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        d: LeftState | RightState = ldata[q]
        if d[0] == "S":
            for p, a in ((0, P0), (1, P1)):
                z = L(("V", p, I, I, -1))
                lt[q, a] = z
                dq.append(z)
        elif d[0] == "V":
            _, p, first, last, prev = d
            for s in vals:
                m = lab(s, b)
                nf = first if first != I else m
                nl = m if m != I else last
                z = L(("V", p, nf, nl, s))
                lt[q, s] = z
                dq.append(z)
            lt[q, E] = done
    left = DFA(
        alphabet, sL, lt, tuple(range(len(ldata))), {i: d for i, d in enumerate(ldata)}
    )

    # RIGHT DFA scans from END backwards. data:
    # ('S',) empty suffix after whole word; ('A',seen,center,first_excl);
    # ('D',) after parity.
    rdata: list[RightState] = []
    rid = {}
    rt = {}

    def R(x: RightState) -> int:
        if x not in rid:
            rid[x] = len(rdata)
            rdata.append(x)
        return rid[x]

    sR = R(("S",))
    after = R(("A", 0, I, I))
    rdone = R(("D",))
    rt[sR, E] = after
    dq = deque([after])
    seen = set()
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        current = rdata[q]
        assert current[0] == "A"
        _, seenval, center, firstex = current
        for s in vals:
            m = lab(s, b)
            if not seenval:
                nd: RightState = ("A", 1, m, I)
            else:
                nd = ("A", 1, center, m if m != I else firstex)
            z = R(nd)
            rt[q, s] = z
            dq.append(z)
        # Once all values have been scanned, the parity tag is consumed.
        rt[q, P0] = rdone
        rt[q, P1] = rdone
    right = DFA(
        alphabet,
        sR,
        rt,
        tuple(range(len(rdata))),
        {i: d for i, d in enumerate(rdata)},
        right=True,
    )

    out: dict[tuple[int, int, int], tuple[int, ...]] = {}
    # Output parity tag using entire suffix summary in right state.
    for p, a in ((0, P0), (1, P1)):
        for r in right.states:
            d = right.data[r]
            if d[0] != "A" or not d[1]:
                continue
            _, _, center, firstex = d
            fa = firstex if firstex != I else center
            g = int(fa == R1)
            out[sL, a, r] = (ptag(p ^ g, b),)
    # Value outputs.
    for states_left_state in left.states:
        ld = left.data[states_left_state]
        if ld[0] != "V":
            continue
        _, p, firstpre, lastpre, prev = ld
        for s in vals:
            m = lab(s, b)
            lastafter = m if m != I else lastpre
            for r in right.states:
                rd = right.data[r]
                if rd[0] != "A":
                    continue
                _, seenval, center, firstex = rd
                firstall = firstex if firstex != I else (center if seenval else I)
                glob = firstpre if firstpre != I else (m if m != I else firstall)
                g = int(glob == R1)
                Li = carry_label(lastpre)
                Li1 = carry_label(lastafter)
                if p == 0:
                    Rip1_lab = firstall if firstall != I else lastafter
                    Ri_lab = m if m != I else (firstall if firstall != I else lastpre)
                else:
                    if firstex != I:
                        Rip1_lab = firstex
                    elif seenval:
                        Rip1_lab = center if center != I else lastafter
                    else:
                        Rip1_lab = lastpre
                    if m != I:
                        Ri_lab = m
                    elif firstex != I:
                        Ri_lab = firstex
                    elif seenval and center != I:
                        Ri_lab = center
                    else:
                        Ri_lab = lastpre
                Ri = carry_label(Ri_lab)
                Rip1 = carry_label(Rip1_lab)
                if not g:
                    y = 2 * s + Li + Rip1 - b * (Li1 + Ri)
                else:
                    if prev == -1:
                        y = s + 1 - b * Li1
                    else:
                        Rim1 = 0 if prev < b - 1 else (Ri if prev == b - 1 else 1)
                        y = s + prev + Li + Ri - b * (Li1 + Rim1)
                if 0 <= y <= 2 * (b - 1):
                    out[states_left_state, s, r] = (y,)
    # END output. r_after END is the right start state.
    for states_left_state in left.states:
        ld = left.data[states_left_state]
        if ld[0] != "V" or ld[4] == -1:
            continue
        _, p, first, last, prev = ld
        g = int(first == R1)
        extra = []
        if p == 0 and g:
            Lh = carry_label(last)
            nextc = 0 if prev < b - 1 else (Lh if prev == b - 1 else 1)
            center = 2 * prev + 2 * Lh - 2 * b * nextc
            if not 0 <= center <= 2 * (b - 1):
                continue
            extra.append(center)
        out[states_left_state, E, sR] = tuple(extra + [E])
    return Bimachine(b, alphabet, left, right, out)


def ref(
    parity: int, half: list[int] | tuple[int, ...] | tuple[int, int], b: int = 10
) -> tuple[int, tuple[int, ...]]:
    h = tuple(half)
    full = h + (h[-2::-1] if parity else h[::-1])
    d = len(full)
    t = b - 1
    L = [0] * (d + 1)
    for i, s in enumerate(full):
        L[i + 1] = 0 if s < t else (L[i] if s == t else 1)
    R = [0] * (d + 1)
    for i in range(d - 1, -1, -1):
        s = full[i]
        R[i] = 0 if s < t else (R[i + 1] if s == t else 1)
    g = L[d]
    if not g:
        o = [2 * full[i] + L[i] + R[i + 1] - b * (L[i + 1] + R[i]) for i in range(d)]
    else:
        o = [0] * (d + 1)
        o[0] = full[0] + 1 - b * L[1]
        o[d] = o[0]
        for i in range(1, d):
            o[i] = full[i] + full[i - 1] + L[i] + R[i] - b * (L[i + 1] + R[i - 1])
    return len(o) & 1, tuple(o[: (len(o) + 1) // 2])


def encode(p: int, h: Sequence[int], b: int = 10) -> tuple[int, ...]:
    return (ptag(p, b),) + tuple(h) + (endtag(b),)


def decode(w: Sequence[int], b: int = 10) -> tuple[int, tuple[int, ...]]:
    assert w[-1] == endtag(b)
    return w[0] - (2 * b - 1), tuple(w[1:-1])


# Determinize an NFA over triples. NFA transitions are represented by adjacency
# mapping (state,a)->set(next). Only reachable subsets are kept.
def determinize(
    alphabet: tuple[int, ...],
    startset: Iterable[int],
    nfa_trans: Mapping[tuple[int, int], AbstractSet[int]],
    data: Sequence[object],
    right: bool = False,
) -> DFA[frozenset[int]]:
    subsets: list[frozenset[int]] = []
    sid = {}

    def S(x: Iterable[int]) -> int:
        frozen = frozenset(x)
        if frozen not in sid:
            sid[frozen] = len(subsets)
            subsets.append(frozen)
        return sid[frozen]

    start = S(startset)
    trans = {}
    dq = deque([start])
    seen = set()
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        A = subsets[q]
        for a in alphabet:
            B: set[int] = set()
            for x in A:
                B.update(nfa_trans.get((x, a), ()))
            if not B:
                continue
            z = S(B)
            trans[q, a] = z
            if z not in seen:
                dq.append(z)
    return DFA(
        alphabet,
        start,
        trans,
        tuple(range(len(subsets))),
        {i: subsets[i] for i in range(len(subsets))},
        right=right,
    )


def compose_bimachine(B1: Bimachine, B2: Bimachine) -> Bimachine:
    assert B1.alphabet == B2.alphabet
    A = B1.alphabet
    # Left NFA triples (l1,r1,l2). Start {sL1} x R1 x {sL2}.
    LT: list[tuple[int, int, int]] = []
    li = {}

    def LID(x: tuple[int, int, int]) -> int:
        if x not in li:
            li[x] = len(LT)
            LT.append(x)
        return li[x]

    lstart = {LID((B1.left.start, r, B2.left.start)) for r in B1.right.states}
    lnfa: dict[tuple[int, int], set[int]] = {}
    # Build transitions lazily over all currently discovered triples; closure may add.
    dq = deque(lstart)
    seen = set()
    while dq:
        qi = dq.popleft()
        if qi in seen:
            continue
        seen.add(qi)
        l1, r1, l2 = LT[qi]
        for a in A:
            l1n = B1.left.step(l1, a)
            if l1n is None:
                continue
            # Need r2 such that delta_R1(r2,a)=r1.
            for r2 in B1.right.states:
                if B1.right.step(r2, a) != r1:
                    continue
                v = B1.out.get((l1, a, r2))
                if v is None:
                    continue
                l2n = B2.left.word(l2, v)
                if l2n is None:
                    continue
                qn = LID((l1n, r2, l2n))
                lnfa.setdefault((qi, a), set()).add(qn)
                if qn not in seen:
                    dq.append(qn)
    left = determinize(A, lstart, lnfa, LT, right=False)

    # Right NFA triples (l1,r1,r2). Start L1 x {sR1} x {sR2}.
    RT: list[tuple[int, int, int]] = []
    ri = {}

    def RID(x: tuple[int, int, int]) -> int:
        if x not in ri:
            ri[x] = len(RT)
            RT.append(x)
        return ri[x]

    rstart = {
        RID((left_state, B1.right.start, B2.right.start))
        for left_state in B1.left.states
    }
    rnfa: dict[tuple[int, int], set[int]] = {}
    dq = deque(rstart)
    seen = set()
    while dq:
        qi = dq.popleft()
        if qi in seen:
            continue
        seen.add(qi)
        l2, r2, rr2 = RT[qi]  # state after symbol in left-index convention
        for a in A:
            # find l1 with deltaL1(l1,a)=l2 and r1=deltaR1(r2,a)
            previous_r1 = B1.right.step(r2, a)
            if previous_r1 is None:
                continue
            for l1 in B1.left.states:
                if B1.left.step(l1, a) != l2:
                    continue
                v = B1.out.get((l1, a, r2))
                if v is None:
                    continue
                # right automaton consumes reversed output word
                # DFA.word on right already reverses its argument, so pass v directly.
                rr1 = B2.right.word(rr2, v)
                if rr1 is None:
                    continue
                qn = RID((l1, previous_r1, rr1))
                rnfa.setdefault((qi, a), set()).add(qn)
                if qn not in seen:
                    dq.append(qn)
    right = determinize(A, rstart, rnfa, RT, right=True)

    # Output function. Search compatible witnesses; theorem guarantees uniqueness.
    out = {}
    for Ls in left.states:
        LA = left.data[Ls]
        for a in A:
            Lnext = left.step(Ls, a)
            if Lnext is None:
                continue
            for Rs in right.states:
                RB = right.data[Rs]  # right state after current symbol
                candidates = set()
                for xid in LA:
                    l1, r1, l2 = LT[xid]
                    l1n = B1.left.step(l1, a)
                    if l1n is None:
                        continue
                    for yid in RB:
                        l1b, r1b, r2b = RT[yid]
                        if l1b != l1n:
                            continue
                        # RB tuple is (l1_after, r1_after, r2_after)
                        r1_after = r1b
                        if B1.right.step(r1_after, a) != r1:
                            continue
                        v = B1.out.get((l1, a, r1_after))
                        if v is None:
                            continue
                        # l2 before output is in LA; r2 after output is r2b
                        w = eval_bimachine_fragment(B2, l2, v, r2b)
                        if w is not None:
                            candidates.add(w)
                if len(candidates) > 1:
                    raise AssertionError(
                        ("ambiguous composed output", len(candidates), a, Ls, Rs)
                    )
                if candidates:
                    out[Ls, a, Rs] = next(iter(candidates))
    C = Bimachine(B1.base, A, left, right, out)
    return pseudo_minimize(C)


def eval_bimachine_fragment(
    B: Bimachine, left_state: int, word: Sequence[int], r_after: int
) -> tuple[int, ...] | None:
    w = tuple(word)
    ls = [left_state]
    for a in w:
        q = B.left.step(ls[-1], a)
        if q is None:
            return None
        ls.append(q)
    rs = [0] * (len(w) + 1)
    rs[len(w)] = r_after
    for i in range(len(w) - 1, -1, -1):
        q = B.right.step(rs[i + 1], w[i])
        if q is None:
            return None
        rs[i] = q
    z: list[int] = []
    for i, a in enumerate(w):
        o = B.out.get((ls[i], a, rs[i + 1]))
        if o is None:
            return None
        z.extend(o)
    return tuple(z)


def minimize_colored(
    dfa: DFA[object], color: Callable[[int], Hashable]
) -> tuple[DFA[tuple[int, ...]], dict[int, int]]:
    qs = list(dfa.states)
    alphabet = dfa.alphabet
    part: dict[int, int] = {}
    classes: dict[Hashable, int] = {}
    for q in qs:
        c = color(q)
        classes.setdefault(c, len(classes))
        part[q] = classes[c]
    while True:
        classes = {}
        new = {}
        for q in qs:
            sig = (
                color(q),
                tuple(
                    part.get(target, -1)
                    if (target := dfa.step(q, a)) is not None
                    else -1
                    for a in alphabet
                ),
            )
            classes.setdefault(sig, len(classes))
            new[q] = classes[sig]
        if len(set(new.values())) == len(set(part.values())):
            part = new
            break
        part = new
    reps: dict[int, int] = {}
    for q, c in part.items():
        reps.setdefault(c, q)
    cmap = {c: i for i, c in enumerate(sorted(reps))}
    trans = {}
    for c, q in reps.items():
        nq = cmap[c]
        for a in alphabet:
            z = dfa.step(q, a)
            if z is not None:
                trans[nq, a] = cmap[part[z]]
    start = cmap[part[dfa.start]]
    data = {cmap[c]: tuple(q for q in qs if part[q] == c) for c in reps}
    return DFA(
        alphabet, start, trans, tuple(range(len(reps))), data, right=dfa.right
    ), {q: part[q] for q in qs}


def pseudo_minimize(B: Bimachine) -> Bimachine:
    # Alternate coloured minimization to a fixed point. Colors encode the entire
    # currently fixed opposite-side output row/column, preserving the function.
    changed = True
    while changed:
        changed = False
        Rstates = B.right.states

        def lc(
            left_state: int, B: Bimachine = B, Rstates: tuple[int, ...] = Rstates
        ) -> tuple[tuple[int, ...] | None, ...]:
            return tuple(
                B.out.get((left_state, a, r), None) for a in B.alphabet for r in Rstates
            )

        Lnew, _lpart = minimize_colored(B.left, lc)
        if len(Lnew.states) < len(B.left.states):
            # representative old state per new class
            rep = {new: members[0] for new, members in Lnew.data.items()}
            out = {
                (nl, a, r): B.out[(old, a, r)]
                for nl, old in rep.items()
                for a in B.alphabet
                for r in Rstates
                if (old, a, r) in B.out
            }
            B = Bimachine(B.base, B.alphabet, Lnew, B.right, out)
            changed = True
        Lstates = B.left.states

        def rc(
            r: int, B: Bimachine = B, Lstates: tuple[int, ...] = Lstates
        ) -> tuple[tuple[int, ...] | None, ...]:
            return tuple(
                B.out.get((left_state, a, r), None)
                for left_state in Lstates
                for a in B.alphabet
            )

        Rnew, _rpart = minimize_colored(B.right, rc)
        if len(Rnew.states) < len(B.right.states):
            rep = {new: members[0] for new, members in Rnew.data.items()}
            out = {
                (left_state, a, nr): B.out[(left_state, a, old)]
                for nr, old in rep.items()
                for left_state in Lstates
                for a in B.alphabet
                if (left_state, a, old) in B.out
            }
            B = Bimachine(B.base, B.alphabet, B.left, Rnew, out)
            changed = True
    return B


def selftest() -> None:
    b = 10
    B = build_step(b)
    print("B1 L/R/out", len(B.left.states), len(B.right.states), len(B.out), flush=True)
    rng = random.Random(196)
    for _ in range(1000):
        p = rng.randrange(2)
        h = [rng.randrange(19) for _ in range(rng.randrange(1, 8))]
        h[0] = h[0] or 1
        got = decode(B.output(encode(p, h, b)), b)
        exp = ref(p, h, b)
        assert got == exp, (p, h, got, exp)
    P = B
    for e in range(1, 5):
        t = time.perf_counter()
        P = compose_bimachine(P, P)
        dt = time.perf_counter() - t
        print(
            "pow",
            2**e,
            "L/R/out",
            len(P.left.states),
            len(P.right.states),
            len(P.out),
            "sec",
            dt,
            flush=True,
        )
        for _ in range(100):
            p = rng.randrange(2)
            h = [rng.randrange(19) for _ in range(rng.randrange(1, 5))]
            h[0] = h[0] or 1
            pp, hh = p, tuple(h)
            for __ in range(2**e):
                pp, hh = ref(pp, hh, b)
            got = decode(P.output(encode(p, h, b)), b)
            assert got == (pp, hh), (e, p, h, got, (pp, hh))


if __name__ == "__main__":
    selftest()
