from __future__ import annotations

import json
import time
from collections import defaultdict, deque
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import NotRequired, TypedDict

from devtools.paths import report_output
from devtools.proofs.builders.bimachine_lazy_power import (
    LazyBimachine,
    compose,
    lazy_from_eager,
)
from devtools.proofs.builders.bimachine_power import build_step
from number_compiler.hashlife.execution.cascade import (
    CascadeRelation,
    GroupedDependencyCascadeArena,
)


class CascadeReport(TypedDict):
    left: dict[str, int]
    right: dict[str, int]
    left_sec: float
    right_sec: float
    left_capped: NotRequired[bool]
    right_capped: NotRequired[bool]


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def values(mask: int) -> Iterator[int]:
    while mask:
        z = mask & -mask
        yield z.bit_length() - 1
        mask -= z


@dataclass
class GDFA:
    alphabet: tuple[int, ...]
    start: int
    trans: dict[tuple[int, int], int]
    states: tuple[int, ...]
    relations: dict[int, CascadeRelation]
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


class RelationStates:
    def __init__(self) -> None:
        self.arena = GroupedDependencyCascadeArena(3)
        self.byroot: dict[int, int] = {}
        self.rels: list[CascadeRelation] = []

    def intern_boxes(self, boxes: Iterable[Sequence[int]]) -> int:
        rel = self.arena.encode_boxes(boxes)
        q = self.byroot.get(rel.root)
        if q is None:
            q = len(self.rels)
            self.byroot[rel.root] = q
            self.rels.append(rel)
        return q

    def boxes(self, q: int) -> tuple[tuple[int, ...], ...]:
        return tuple(self.arena.iter_boxes(self.rels[q]))


class BehaviorCache:
    def __init__(self, B1: LazyBimachine, B2: LazyBimachine) -> None:
        self.B1 = B1
        self.B2 = B2
        self.emit: dict[tuple[int, int, int], tuple[int, ...] | None] = {}
        self.left_classes: dict[
            tuple[int, int], tuple[tuple[int, tuple[int, ...], int], ...]
        ] = {}
        self.right_classes: dict[
            tuple[int, int, int], tuple[tuple[tuple[int, ...], int], ...]
        ] = {}
        self.left_image: dict[tuple[int, tuple[int, ...]], int] = {}
        self.right_image: dict[tuple[int, tuple[int, ...]], int] = {}

    def _emit(self, left_state: int, a: int, r: int) -> tuple[int, ...] | None:
        k = (left_state, a, r)
        if k not in self.emit:
            self.emit[k] = self.B1.emit(left_state, a, r)
        return self.emit[k]

    def left_behavior(
        self, a: int, r2: int
    ) -> tuple[tuple[int, tuple[int, ...], int], ...]:
        # classes: (pre-mask of l1, emitted word, next l1)
        k = (a, r2)
        z = self.left_classes.get(k)
        if z is not None:
            return z
        g: defaultdict[tuple[tuple[int, ...], int], int] = defaultdict(int)
        for l1 in self.B1.left.states:
            l1n = self.B1.left.step(l1, a)
            if l1n is None:
                continue
            v = self._emit(l1, a, r2)
            if v is not None:
                g[(v, l1n)] |= 1 << l1
        z = tuple((mask, v, l1n) for (v, l1n), mask in g.items())
        self.left_classes[k] = z
        return z

    def image_left(self, mask: int, word: tuple[int, ...]) -> int:
        k = (mask, word)
        z = self.left_image.get(k)
        if z is not None:
            return z
        out = 0
        for left_state in values(mask):
            q = self.B2.left.word(left_state, word)
            if q is not None:
                out |= 1 << q
        self.left_image[k] = out
        return out

    def right_behavior(
        self, a: int, r2: int, l2mask: int
    ) -> tuple[tuple[tuple[int, ...], int], ...]:
        # group predecessor l1 by emitted word without iterating rr2.
        k = (a, r2, l2mask)
        z = self.right_classes.get(k)
        if z is not None:
            return z
        g: defaultdict[tuple[int, ...], int] = defaultdict(int)
        # Build predecessor mapping lazily by scanning B1.left states once.
        for l1 in self.B1.left.states:
            l2 = self.B1.left.step(l1, a)
            if l2 is None or not ((l2mask >> l2) & 1):
                continue
            v = self._emit(l1, a, r2)
            if v is not None:
                g[v] |= 1 << l1
        z = tuple(g.items())
        self.right_classes[k] = z
        return z

    def image_right(self, mask: int, word: tuple[int, ...]) -> int:
        k = (mask, word)
        z = self.right_image.get(k)
        if z is not None:
            return z
        out = 0
        for r in values(mask):
            q = self.B2.right.word(r, word)
            if q is not None:
                out |= 1 << q
        self.right_image[k] = out
        return out


def build_left(
    B1: LazyBimachine, B2: LazyBimachine, cap: int = 100000, time_cap: float = 120.0
) -> tuple[GDFA, RelationStates, BehaviorCache, bool, float]:
    A = B1.alphabet
    S = RelationStates()
    C = BehaviorCache(B1, B2)
    # order: l1,l2,r1. initial is one Cartesian box.
    allr = sum(1 << r for r in B1.right.states)
    start = S.intern_boxes(((1 << B1.left.start, 1 << B2.left.start, allr),))
    # preimage of right transition: selector r1 -> selector r2
    pred_cache: dict[tuple[int, int], int] = {}

    def pred_mask(a: int, r1mask: int) -> int:
        k = (a, r1mask)
        z = pred_cache.get(k)
        if z is not None:
            return z
        out = 0
        for r2 in B1.right.states:
            r1 = B1.right.step(r2, a)
            if r1 is not None and ((r1mask >> r1) & 1):
                out |= 1 << r2
        pred_cache[k] = out
        return out

    trans = {}
    dq = deque([start])
    seen = set()
    t0 = time.perf_counter()
    capped = False
    while dq:
        if time.perf_counter() - t0 > time_cap:
            capped = True
            break
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        boxes = S.boxes(q)
        for a in A:
            out = []
            for l1mask, l2mask, r1mask in boxes:
                r2mask = pred_mask(a, r1mask)
                for r2 in values(r2mask):
                    for premask, v, l1n in C.left_behavior(a, r2):
                        if not (l1mask & premask):
                            continue
                        l2nmask = C.image_left(l2mask, v)
                        if l2nmask:
                            out.append((1 << l1n, l2nmask, 1 << r2))
            if not out:
                continue
            z = S.intern_boxes(out)
            trans[q, a] = z
            if z not in seen:
                if len(S.rels) >= cap:
                    capped = True
                    dq.clear()
                    break
                dq.append(z)
    return (
        GDFA(
            A,
            start,
            trans,
            tuple(range(len(S.rels))),
            {i: S.rels[i] for i in range(len(S.rels))},
        ),
        S,
        C,
        capped,
        time.perf_counter() - t0,
    )


def build_right(
    B1: LazyBimachine, B2: LazyBimachine, cap: int = 100000, time_cap: float = 120.0
) -> tuple[GDFA, RelationStates, BehaviorCache, bool, float]:
    A = B1.alphabet
    S = RelationStates()
    C = BehaviorCache(B1, B2)
    # order: l2,rr2,r2 for source triple (l2,r2,rr2).
    alll = sum(1 << left_state for left_state in B1.left.states)
    start = S.intern_boxes(((alll, 1 << B2.right.start, 1 << B1.right.start),))
    trans = {}
    dq = deque([start])
    seen = set()
    t0 = time.perf_counter()
    capped = False
    while dq:
        if time.perf_counter() - t0 > time_cap:
            capped = True
            break
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        boxes = S.boxes(q)
        for a in A:
            out = []
            for l2mask, rr2mask, r2mask in boxes:
                for r2 in values(r2mask):
                    r1 = B1.right.step(r2, a)
                    if r1 is None:
                        continue
                    for v, l1mask in C.right_behavior(a, r2, l2mask):
                        rr1mask = C.image_right(rr2mask, v)
                        if rr1mask:
                            out.append((l1mask, rr1mask, 1 << r1))
            if not out:
                continue
            z = S.intern_boxes(out)
            trans[q, a] = z
            if z not in seen:
                if len(S.rels) >= cap:
                    capped = True
                    dq.clear()
                    break
                dq.append(z)
    return (
        GDFA(
            A,
            start,
            trans,
            tuple(range(len(S.rels))),
            {i: S.rels[i] for i in range(len(S.rels))},
            right=True,
        ),
        S,
        C,
        capped,
        time.perf_counter() - t0,
    )


def metrics(S: RelationStates) -> dict[str, int]:
    m = S.arena.metrics()
    return {
        "states": len(S.rels),
        "dependency_nodes": m.dependency_nodes,
        "dependency_groups": m.dependency_edges,
        "description_bits": m.description_bits,
        "relation_cardinality": sum(r.cardinality for r in S.rels),
    }


def main() -> None:
    B = lazy_from_eager(build_step(10))
    flat2 = compose(B, B, verbose=False)
    L2, LS2, _, _lc2, sl2 = build_left(B, B, cap=5000, time_cap=60)
    R2, RS2, _, _rc2, sr2 = build_right(B, B, cap=5000, time_cap=60)
    assert len(L2.states) == len(flat2.left.states), (
        len(L2.states),
        len(flat2.left.states),
    )
    assert len(R2.states) == len(flat2.right.states), (
        len(R2.states),
        len(flat2.right.states),
    )
    out: dict[str, CascadeReport] = {
        "T2": {
            "left": metrics(LS2),
            "right": metrics(RS2),
            "left_sec": sl2,
            "right_sec": sr2,
        }
    }
    # Use the already verified flat T2 resolver; grouped states are a separate
    # equivalent determinization and not assumed to share numeric state ids.
    # T4 grouped context construction therefore uses flat T2 component DFAs.
    _L4, LS4, _, capL4, sl4 = build_left(flat2, flat2, cap=100, time_cap=20)
    _R4, RS4, _, capR4, sr4 = build_right(flat2, flat2, cap=100, time_cap=20)
    out["T4_probe"] = {
        "left": metrics(LS4),
        "right": metrics(RS4),
        "left_sec": sl4,
        "right_sec": sr4,
        "left_capped": capL4,
        "right_capped": capR4,
    }
    (
        report_output(
            "devtools.proofs.builders.grouped_cascade_power",
            "grouped_cascade_metrics.json",
        )
    ).write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))
    (
        report_output(
            "devtools.proofs.builders.grouped_cascade_power",
            "GROUPED_CASCADE_RESULTS.md",
        )
    ).write_text(
        f"""# Grouped dependency-cascade power probe\n\nThis implementation determinizes composed bimachine contexts directly as grouped dependency functions (MDD/cascade boxes), never as flat subsets of Cartesian triples.\n\n## T2 exact\n\n- left: {out["T2"]["left"]["states"]:,} states, {out["T2"]["left"]["dependency_groups"]:,} dependency groups\n- right: {out["T2"]["right"]["states"]:,} states, {out["T2"]["right"]["dependency_groups"]:,} dependency groups\n- state counts exactly match the verified classical T2 bimachine.\n\n## T4 probe\n\n- left: {out["T4_probe"]["left"]["states"]:,} discovered states / {out["T4_probe"]["left"]["dependency_groups"]:,} dependency groups, capped={capL4}\n- right: {out["T4_probe"]["right"]["states"]:,} discovered states / {out["T4_probe"]["right"]["dependency_groups"]:,} dependency groups, capped={capR4}\n\nThe hierarchy removes the full wreath-product tuple storage.  A full-J promotion still requires the number of distinct top-level sections, not only their internal dependency representation, to remain polylogarithmic under powering.\n"""
    )


if __name__ == "__main__":
    main()
