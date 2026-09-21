from __future__ import annotations

from array import array
from collections import deque

from number_compiler.arithmetic.automata.transducer import LazyBimachine


def lcp2(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    n = min(len(a), len(b))
    i = 0
    while i < n and a[i] == b[i]:
        i += 1
    return a[:i]


def left_earliest(
    machine: LazyBimachine,
) -> LazyBimachine:
    L = len(machine.left.states)
    R = len(machine.right.states)
    A = machine.alphabet
    assert machine.left.states == tuple(range(L)) and machine.right.states == tuple(
        range(R)
    )
    deadL = [
        q
        for q in machine.left.states
        if all(machine.left.step(q, a) is None for a in A)
    ]
    print("deadL", deadL)
    terminals = {q * R + machine.right.start for q in deadL}
    # inverse left transitions and right predecessor-after lists
    lpre: dict[int, list[list[int]]] = {a: [[] for _ in range(L)] for a in A}
    rafter: dict[int, list[list[int]]] = {a: [[] for _ in range(R)] for a in A}
    for a in A:
        for left_state in range(L):
            z = machine.left.step(left_state, a)
            if z is not None:
                lpre[a][z].append(left_state)
        for r2 in range(R):
            rb = machine.right.step(r2, a)
            if rb is not None:
                rafter[a][rb].append(r2)
    N = L * R
    co = bytearray(N)
    witness: list[tuple[int, ...] | None] = [None] * N
    rev = [array("I") for _ in range(N)]
    dq = deque(terminals)
    for t in terminals:
        co[t] = 1
        witness[t] = ()
    emit_calls = 0
    while dq:
        tid = dq.popleft()
        target_left, r2 = divmod(tid, R)
        for a in A:
            rb = machine.right.step(r2, a)
            if rb is None:
                continue
            for l1 in lpre[a][target_left]:
                w = machine.emit(l1, a, r2)
                emit_calls += 1
                if w is None:
                    continue
                pid = l1 * R + rb
                rev[tid].append(pid)
                if not co[pid]:
                    co[pid] = 1
                    suffix = witness[tid]
                    assert suffix is not None
                    witness[pid] = w + suffix
                    dq.append(pid)
    print(
        "co",
        sum(co),
        "N",
        N,
        "emit bfs",
        emit_calls,
        "revedges",
        sum(len(x) for x in rev),
        "maxwit",
        max(map(len, (w for w in witness if w is not None)), default=0),
    )
    alpha = list(witness)
    q = deque(i for i in range(N) if co[i])
    inq = bytearray(co)
    updates = 0
    scans = 0
    while q:
        vid = q.popleft()
        inq[vid] = 0
        left_state, rb = divmod(vid, R)
        cand: tuple[int, ...] | None = () if vid in terminals else None
        for a in A:
            l2 = machine.left.step(left_state, a)
            if l2 is None:
                continue
            for r2 in rafter[a][rb]:
                tid = l2 * R + r2
                if not co[tid]:
                    continue
                w = machine.emit(left_state, a, r2)
                scans += 1
                if w is None:
                    continue
                suffix = alpha[tid]
                assert suffix is not None
                candidate_word = w + suffix
                cand = candidate_word if cand is None else lcp2(cand, candidate_word)
                if cand == ():
                    break
            if cand == ():
                break
        if cand is None:
            continue
        if alpha[vid] != cand:
            previous = alpha[vid]
            assert previous is None or len(cand) <= len(previous)
            alpha[vid] = cand
            updates += 1
            for p in rev[vid]:
                if not inq[p]:
                    q.append(p)
                    inq[p] = 1
    print(
        "updates",
        updates,
        "scans",
        scans,
        "alphadist",
        __import__("collections").Counter(len(x) for x in alpha if x is not None),
    )

    def emit(left_state: int, a: int, r2: int) -> tuple[int, ...] | None:
        orig = machine.emit(left_state, a, r2)
        if orig is None:
            return None
        rb = machine.right.step(r2, a)
        l2 = machine.left.step(left_state, a)
        if rb is None or l2 is None:
            return None
        before = alpha[left_state * R + rb]
        after = alpha[l2 * R + r2]
        if before is None or after is None:
            return orig
        combined = orig + after
        if left_state == machine.left.start:
            return combined
        if combined[: len(before)] != before:
            raise AssertionError(("prefix", left_state, a, r2, before, combined))
        return combined[len(before) :]

    return LazyBimachine(
        machine.base, A, machine.left, machine.right, emit, cache_enabled=False
    )


if __name__ == "__main__":
    import random
    import time

    from devtools.experiments.reverse_add.power import compose_bimachines
    from number_compiler.arithmetic.automata.transducer import (
        build_pair_step_bimachine,
        encode_pair_half,
    )
    from number_compiler.arithmetic.functions.residual import minimize_bimachine

    b = minimize_bimachine(build_pair_step_bimachine(10)).machine
    t = time.perf_counter()
    e = left_earliest(b)
    print("earliest1", time.perf_counter() - t)
    q = minimize_bimachine(e)
    print("min1", len(q.machine.left.states), len(q.machine.right.states), q.metrics)
    # exact check
    rng = random.Random(1)
    for _ in range(100):
        w = encode_pair_half(
            rng.randrange(2),
            [rng.randrange(19) for _ in range(rng.randrange(1, 8))],
            10,
        )
        assert e.output(w) == b.output(w)
    c = compose_bimachines(q.machine, q.machine, state_cap=10000, time_cap=20).machine
    print("compose2", len(c.left.states), len(c.right.states))
    t = time.perf_counter()
    e2 = left_earliest(c)
    print("earliest2", time.perf_counter() - t)
    t = time.perf_counter()
    q2 = minimize_bimachine(e2)
    print(
        "min2",
        len(q2.machine.left.states),
        len(q2.machine.right.states),
        time.perf_counter() - t,
        q2.metrics,
    )


def mirror_machine(
    machine: LazyBimachine,
) -> LazyBimachine:
    from number_compiler.arithmetic.automata.transducer import DFA, LazyBimachine

    A = machine.alphabet
    left = DFA(
        A, machine.right.start, dict(machine.right.trans), machine.right.states, False
    )
    right = DFA(
        A, machine.left.start, dict(machine.left.trans), machine.left.states, True
    )

    def emit(left_state: int, a: int, r: int) -> None | tuple[int, ...]:
        w = machine.emit(r, a, left_state)
        return None if w is None else tuple(reversed(w))

    return LazyBimachine(machine.base, A, left, right, emit, cache_enabled=False)


def right_earliest(
    machine: LazyBimachine,
) -> LazyBimachine:
    return mirror_machine(left_earliest(mirror_machine(machine)))


if __name__ == "__main__":
    print("--- right after left T1 ---")
    er = right_earliest(e)
    qr = minimize_bimachine(er)
    print(
        "LRmin1", len(qr.machine.left.states), len(qr.machine.right.states), qr.metrics
    )
    import random

    rng = random.Random(2)
    for _ in range(100):
        w = encode_pair_half(
            rng.randrange(2),
            [rng.randrange(19) for _ in range(rng.randrange(1, 8))],
            10,
        )
        assert er.output(w) == b.output(w)
    print("--- right after left T2 ---")
    t = time.perf_counter()
    er2 = right_earliest(e2)
    print("right2", time.perf_counter() - t)
    t = time.perf_counter()
    qr2 = minimize_bimachine(er2)
    print(
        "LRmin2",
        len(qr2.machine.left.states),
        len(qr2.machine.right.states),
        time.perf_counter() - t,
        qr2.metrics,
    )
