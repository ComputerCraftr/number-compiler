from __future__ import annotations

from collections.abc import Callable, Mapping

from devtools.proofs.builders.bimachine_power import DFA, Bimachine


def _refine(
    states: tuple[int, ...],
    alphabet: tuple[int, ...],
    step: Callable[[int, int], int | None],
    obs_ids: Mapping[tuple[int, int], int],
) -> dict[int, int]:
    part = {q: 0 for q in states}
    while True:
        ids: dict[tuple[tuple[int | None, int], ...], int] = {}
        new = {}
        for q in states:
            sig = tuple(
                (
                    None if (target := step(q, a)) is None else part[target],
                    obs_ids[(q, a)],
                )
                for a in alphabet
            )
            ids.setdefault(sig, len(ids))
            new[q] = ids[sig]
        if len(set(new.values())) == len(set(part.values())):
            return new
        part = new


def minimize_eager(B: Bimachine) -> Bimachine:
    A = B.alphabet
    L = tuple(B.left.states)
    R = tuple(B.right.states)
    # Output behavior is partition-independent: intern it once.  Rebuilding the
    # raw cross-context vector inside every refinement round was an accidental
    # O(iterations * |L| * |R| * |A|) regression for powered bimachines.
    oi: dict[tuple[str, tuple[tuple[int, ...] | None, ...]], int] = {}
    obsL = {}
    obsR = {}
    for left_state in L:
        for a in A:
            vec = tuple(B.out.get((left_state, a, r)) for r in R)
            oi.setdefault(("L", vec), len(oi))
            obsL[(left_state, a)] = oi[("L", vec)]
    for r in R:
        for a in A:
            vec = tuple(B.out.get((left_state, a, r)) for left_state in L)
            oi.setdefault(("R", vec), len(oi))
            obsR[(r, a)] = oi[("R", vec)]
    lp = _refine(L, A, B.left.step, obsL)
    rp = _refine(R, A, B.right.step, obsR)
    lclasses = sorted(set(lp.values()))
    rclasses = sorted(set(rp.values()))
    lrep = {c: next(q for q in L if lp[q] == c) for c in lclasses}
    rrep = {c: next(q for q in R if rp[q] == c) for c in rclasses}
    lm = {c: i for i, c in enumerate(lclasses)}
    rm = {c: i for i, c in enumerate(rclasses)}
    lt = {}
    rt = {}
    for c, q in lrep.items():
        for a in A:
            z = B.left.step(q, a)
            if z is not None:
                lt[(lm[c], a)] = lm[lp[z]]
    for c, q in rrep.items():
        for a in A:
            z = B.right.step(q, a)
            if z is not None:
                rt[(rm[c], a)] = rm[rp[z]]
    left = DFA(
        A,
        lm[lp[B.left.start]],
        lt,
        tuple(range(len(lclasses))),
        {lm[c]: B.left.data[lrep[c]] for c in lclasses},
    )
    right = DFA(
        A,
        rm[rp[B.right.start]],
        rt,
        tuple(range(len(rclasses))),
        {rm[c]: B.right.data[rrep[c]] for c in rclasses},
        right=True,
    )
    out = {}
    for lc, lq in lrep.items():
        for a in A:
            for rc, rq in rrep.items():
                output = B.out.get((lq, a, rq))
                if output is not None:
                    out[(lm[lc], a, rm[rc])] = output
    return Bimachine(B.base, A, left, right, out)
