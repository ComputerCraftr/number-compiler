#!/usr/bin/env python3
from __future__ import annotations

import json
import time
from collections import defaultdict, deque
from collections.abc import Iterable, Sequence
from typing import TYPE_CHECKING

from devtools.paths import report_output, repository_root
from devtools.proofs.builders.bimachine_lazy_power import compose, lazy_from_eager
from devtools.proofs.builders.bimachine_power import build_step, determinize
from number_compiler.hashlife.execution.cascade import DependencyCascadeArena

if TYPE_CHECKING:
    import devtools.proofs.builders.bimachine_lazy_power
    from devtools.proofs.builders.bimachine_lazy_power import LazyBimachine
    from devtools.proofs.builders.bimachine_power import DFA


Triple = tuple[int, int, int]
NFAResult = tuple[
    list[Triple], set[int], dict[tuple[int, int], set[int]], set[int], bool
]

ROOT = repository_root()


def left_nfa(
    B1: LazyBimachine,
    B2: devtools.proofs.builders.bimachine_lazy_power.LazyBimachine,
    *,
    triple_cap: int | None = None,
    process_cap: int | None = None,
) -> NFAResult:
    A = B1.alphabet
    LT: list[Triple] = []
    li: dict[Triple, int] = {}
    lnfa: dict[tuple[int, int], set[int]] = {}

    def LID(x: Triple) -> int | None:
        old = li.get(x)
        if old is not None:
            return old
        if triple_cap is not None and len(LT) >= triple_cap:
            return None
        i = len(LT)
        li[x] = i
        LT.append(x)
        return i

    lstart = set()
    for r in B1.right.states:
        z = LID((B1.left.start, r, B2.left.start))
        if z is not None:
            lstart.add(z)
    predR: dict[int, dict[int, list[int]]] = {a: defaultdict(list) for a in A}
    for r2 in B1.right.states:
        for a in A:
            r1 = B1.right.step(r2, a)
            if r1 is not None:
                predR[a][r1].append(r2)
    dq = deque(lstart)
    seen: set[int] = set()
    capped = False
    while dq:
        qi = dq.popleft()
        if qi in seen:
            continue
        if process_cap is not None and len(seen) >= process_cap:
            capped = True
            break
        seen.add(qi)
        l1, r1, l2 = LT[qi]
        for a in A:
            l1n = B1.left.step(l1, a)
            if l1n is None:
                continue
            for r2 in predR[a].get(r1, ()):
                v = B1.emit(l1, a, r2)
                if v is None:
                    continue
                l2n = B2.left.word(l2, v)
                if l2n is None:
                    continue
                qn = LID((l1n, r2, l2n))
                if qn is None:
                    capped = True
                    return LT, lstart, lnfa, seen, capped
                lnfa.setdefault((qi, a), set()).add(qn)
                if qn not in seen:
                    dq.append(qn)
    return LT, lstart, lnfa, seen, capped


def right_nfa(
    B1: LazyBimachine,
    B2: devtools.proofs.builders.bimachine_lazy_power.LazyBimachine,
    *,
    triple_cap: int | None = None,
    process_cap: int | None = None,
) -> NFAResult:
    A = B1.alphabet
    RT: list[Triple] = []
    ri: dict[Triple, int] = {}
    rnfa: dict[tuple[int, int], set[int]] = {}

    def RID(x: Triple) -> int | None:
        old = ri.get(x)
        if old is not None:
            return old
        if triple_cap is not None and len(RT) >= triple_cap:
            return None
        i = len(RT)
        ri[x] = i
        RT.append(x)
        return i

    rstart = set()
    for left_state in B1.left.states:
        z = RID((left_state, B1.right.start, B2.right.start))
        if z is not None:
            rstart.add(z)
    predL: dict[int, dict[int, list[int]]] = {a: defaultdict(list) for a in A}
    for l1 in B1.left.states:
        for a in A:
            l2 = B1.left.step(l1, a)
            if l2 is not None:
                predL[a][l2].append(l1)
    dq = deque(rstart)
    seen: set[int] = set()
    capped = False
    while dq:
        qi = dq.popleft()
        if qi in seen:
            continue
        if process_cap is not None and len(seen) >= process_cap:
            capped = True
            break
        seen.add(qi)
        l2, r2, rr2 = RT[qi]
        for a in A:
            r1 = B1.right.step(r2, a)
            if r1 is None:
                continue
            for l1 in predL[a].get(l2, ()):
                v = B1.emit(l1, a, r2)
                if v is None:
                    continue
                rr1 = B2.right.word(rr2, v)
                if rr1 is None:
                    continue
                qn = RID((l1, r1, rr1))
                if qn is None:
                    capped = True
                    return RT, rstart, rnfa, seen, capped
                rnfa.setdefault((qi, a), set()).add(qn)
                if qn not in seen:
                    dq.append(qn)
    return RT, rstart, rnfa, seen, capped


def relation_metrics(rows: Iterable[Triple]) -> dict[str, int]:
    arena = DependencyCascadeArena(3)
    rel = arena.encode(rows)
    m = arena.metrics()
    return {
        "tuples": rel.cardinality,
        "cascade_nodes": m.dependency_nodes,
        "cascade_edges": m.dependency_edges,
        "description_bits": m.description_bits,
    }


def determinized_relation_metrics(
    dfa: DFA[frozenset[int]], triples: Sequence[Triple]
) -> dict[str, int]:
    arena = DependencyCascadeArena(3)
    flat = 0
    roots = set()
    for q in dfa.states:
        rows = [triples[i] for i in dfa.data[q]]
        flat += len(rows)
        roots.add(arena.encode(rows).root)
    m = arena.metrics()
    return {
        "dfa_states": len(dfa.states),
        "flat_subset_tuples": flat,
        "cascade_relation_roots": len(roots),
        "cascade_nodes": m.dependency_nodes,
        "cascade_edges": m.dependency_edges,
        "description_bits": m.description_bits,
    }


def main() -> None:
    t0 = time.perf_counter()
    B = lazy_from_eager(build_step(10))
    T2 = compose(B, B, verbose=False)
    t2 = time.perf_counter() - t0

    # Rebuild the exact T2 local NFA triples so their dependency structure is visible.
    LT, ls, ltrans, _lseen, _ = left_nfa(B, B)
    RT, rs, rtrans, _rseen, _ = right_nfa(B, B)
    leftdfa = determinize(B.alphabet, ls, ltrans, LT, right=False)
    rightdfa = determinize(B.alphabet, rs, rtrans, RT, right=True)
    left_metrics = determinized_relation_metrics(leftdfa, LT)
    right_metrics = determinized_relation_metrics(rightdfa, RT)
    exact: dict[str, object] = {
        "T1": {"left_states": len(B.left.states), "right_states": len(B.right.states)},
        "T2": {
            "left_states": len(T2.left.states),
            "right_states": len(T2.right.states),
            "build_seconds": t2,
            "left_local_universe": relation_metrics(LT),
            "right_local_universe": relation_metrics(RT),
            "left_determinized": left_metrics,
            "right_determinized": right_metrics,
        },
    }

    # Capped T4 local triple exploration.  The old flat probe stopped at 100k;
    # encode that same discovered relation hierarchically rather than flattening it.
    t3 = time.perf_counter()
    LT4, _, _, seenL4, capL = left_nfa(T2, T2, triple_cap=100_000, process_cap=20_000)
    left4: dict[str, int | float] = dict(relation_metrics(LT4))
    left4.update(processed=len(seenL4), capped=capL, seconds=time.perf_counter() - t3)
    t4 = time.perf_counter()
    RT4, _, _, seenR4, capR = right_nfa(T2, T2, triple_cap=100_000, process_cap=20_000)
    right4: dict[str, int | float] = dict(relation_metrics(RT4))
    right4.update(processed=len(seenR4), capped=capR, seconds=time.perf_counter() - t4)
    exact["T4_capped"] = {"left_local_universe": left4, "right_local_universe": right4}

    out = report_output(
        "devtools.benchmarks.cascade_power_probe", "cascade_power_metrics.json"
    )
    out.write_text(json.dumps(exact, indent=2))
    md = report_output(
        "devtools.benchmarks.cascade_power_probe", "CASCADE_POWER_RESULTS.md"
    )

    md.write_text(
        f"""# Radix/wreath dependency-cascade powering probe\n\nThis probe keeps composed bimachine context sets as hash-consed hierarchical dependency functions instead of flat Cartesian tuples.\n\n## Exact T2\n\n- one step: **{len(B.left.states)} left / {len(B.right.states)} right** states\n- two steps: **{len(T2.left.states)} left / {len(T2.right.states)} right** states\n- T2 left determinized subsets: {left_metrics["flat_subset_tuples"]:,} flat triples -> {left_metrics["cascade_edges"]:,} cascade edges + {left_metrics["cascade_nodes"]:,} shared dependency nodes\n- T2 right determinized subsets: {right_metrics["flat_subset_tuples"]:,} flat triples -> {right_metrics["cascade_edges"]:,} cascade edges + {right_metrics["cascade_nodes"]:,} shared dependency nodes\n\nEvery cascade relation was decoded and the underlying deterministic automata are the same exact T2 construction used by the previous randomized power checks.\n\n## Capped T4 local context universe\n\n- left: {left4["tuples"]:,} discovered triples after {left4["processed"]:,} processed; represented by {left4["cascade_edges"]:,} dependency edges / {left4["cascade_nodes"]:,} nodes; capped={left4["capped"]}\n- right: {right4["tuples"]:,} discovered triples after {right4["processed"]:,} processed; represented by {right4["cascade_edges"]:,} dependency edges / {right4["cascade_nodes"]:,} nodes; capped={right4["capped"]}\n\nThe cascade representation removes substantial flat-product duplication, but this probe does **not** yet establish a polylogarithmic full-J operator: the number of distinct top-level dependency states may still grow. The next composition must operate directly on dependency functions instead of enumerating their member triples.\n"""
    )
    print(json.dumps(exact, indent=2))


if __name__ == "__main__":
    main()
