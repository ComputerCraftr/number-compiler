from __future__ import annotations

import json
import random
import time
from collections import Counter
from collections.abc import Sequence
from dataclasses import dataclass
from itertools import pairwise
from pathlib import Path

from devtools.paths import report_output
from devtools.verification.builders.bimachine_lazy_power import (
    LazyBimachine,
    lazy_from_eager,
)
from devtools.verification.builders.bimachine_power import (
    build_step,
    decode,
    encode,
    ref,
)
from devtools.verification.sequence_reduction import balanced_reduce
from number_compiler.arithmetic.automata.transducer import transduction_midpoints

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


@dataclass(frozen=True, slots=True)
class N:
    id: int
    kind: str
    length: int
    sym: int | None
    left: int | None
    right: int | None


class SLP:
    def __init__(self) -> None:
        self.nodes: list[N] = []
        self.term: dict[int, int] = {}
        self.catmap: dict[tuple[int, int], int] = {}
        self.empty_id = self._add(N(0, "E", 0, None, None, None))

    def _add(self, n: N) -> int:
        if n.id != len(self.nodes):
            n = N(len(self.nodes), n.kind, n.length, n.sym, n.left, n.right)
        self.nodes.append(n)
        return n.id

    def empty(self) -> int:
        return self.empty_id

    def terminal(self, s: int) -> int:
        s = int(s)
        if s not in self.term:
            self.term[s] = self._add(N(0, "T", 1, s, None, None))
        return self.term[s]

    def cat(self, a: int, b: int) -> int:
        if a == self.empty_id:
            return b
        if b == self.empty_id:
            return a
        k = (a, b)
        z = self.catmap.get(k)
        if z is None:
            z = self._add(
                N(0, "C", self.nodes[a].length + self.nodes[b].length, None, a, b)
            )
            self.catmap[k] = z
        return z

    def word(self, w: Sequence[int]) -> int:
        ids = [self.terminal(x) for x in w]
        if not ids:
            return self.empty()
        return balanced_reduce(ids, self.cat, self.empty)

    def materialize(self, q: int) -> tuple[int, ...]:
        out = []
        stack = [q]
        while stack:
            z = stack.pop()
            n = self.nodes[z]
            if n.kind == "E":
                continue
            if n.kind == "T":
                assert n.sym is not None
                out.append(n.sym)
                continue
            assert n.left is not None and n.right is not None
            stack.append(n.right)
            stack.append(n.left)
        return tuple(out)

    def reachable(self, q: int) -> set[int]:
        seen = set()
        st = [q]
        while st:
            z = st.pop()
            if z in seen:
                continue
            seen.add(z)
            n = self.nodes[z]
            if n.kind == "C":
                assert n.left is not None and n.right is not None
                st.extend((n.left, n.right))
        return seen

    def metrics(self, q: int) -> dict[str, int]:
        r = self.reachable(q)
        return {
            "length": self.nodes[q].length,
            "nodes": len(r),
            "rules": sum(self.nodes[z].kind == "C" for z in r),
        }


def repair_build(arena: SLP, word: tuple[int, ...]) -> int:
    # Exact RePair-like grammar.  Nonterminals are arena nodes and replacement
    # keeps the shared recursive expansion, not a new terminal alphabet.
    seq = [arena.terminal(x) for x in word]
    while len(seq) >= 2:
        cnt = Counter(pairwise(seq))
        (a, b), freq = cnt.most_common(1)[0]
        if freq < 2:
            break
        nt = arena.cat(a, b)
        out = []
        i = 0
        reps = 0
        while i < len(seq):
            if i + 1 < len(seq) and seq[i] == a and seq[i + 1] == b:
                out.append(nt)
                i += 2
                reps += 1
            else:
                out.append(seq[i])
                i += 1
        if reps < 2:
            break
        seq = out
    # balanced concat the top string
    return balanced_reduce(seq, arena.cat, arena.empty)


class BimachineSLP:
    def __init__(self, B: LazyBimachine, arena: SLP) -> None:
        self.B = B
        self.A = arena
        self.fwd: dict[tuple[int, int], int | None] = {}
        self.rev: dict[tuple[int, int], int | None] = {}
        self.emit: dict[tuple[int, int, int], int] = {}
        self.calls = 0

    def _action(self, q: int, state: int, right: bool = False) -> int | None:
        cache = self.rev if right else self.fwd
        root = (q, state)
        if root in cache:
            return cache[root]
        todo = [(q, state, False)]
        while todo:
            node_id, st, expanded = todo.pop()
            key = (node_id, st)
            if key in cache:
                continue
            n = self.A.nodes[node_id]
            if n.kind == "E":
                cache[key] = st
                continue
            if n.kind == "T":
                assert n.sym is not None
                cache[key] = (
                    self.B.right.step(st, n.sym)
                    if right
                    else self.B.left.step(st, n.sym)
                )
                continue
            assert n.left is not None and n.right is not None
            first, second = (n.right, n.left) if right else (n.left, n.right)
            if not expanded:
                todo.append((node_id, st, True))
                todo.append((first, st, False))
                continue
            mid = cache[(first, st)]
            if mid is None:
                cache[key] = None
                continue
            second_key = (second, mid)
            if second_key not in cache:
                todo.append((node_id, st, True))
                todo.append((second, mid, False))
                continue
            cache[key] = cache[second_key]
        return cache[root]

    def forward(self, q: int, left_state: int) -> int | None:
        return self._action(q, left_state, False)

    def reverse(self, q: int, r: int) -> int | None:
        return self._action(q, r, True)

    def block(self, q: int, left_state: int, r: int) -> int:
        root = (q, left_state, r)
        z = self.emit.get(root)
        if z is not None:
            return z
        todo = [(q, left_state, r, False)]
        while todo:
            node_id, lctx, rctx, expanded = todo.pop()
            key = (node_id, lctx, rctx)
            if key in self.emit:
                continue
            if not expanded:
                self.calls += 1
            n = self.A.nodes[node_id]
            if n.kind == "E":
                self.emit[key] = self.A.empty()
                continue
            if n.kind == "T":
                assert n.sym is not None
                w = self.B.emit(lctx, n.sym, rctx)
                if w is None:
                    raise ValueError(("undefined", lctx, n.sym, rctx))
                self.emit[key] = self.A.word(w)
                continue
            assert n.left is not None and n.right is not None
            lm, rm = transduction_midpoints(
                self.forward, self.reverse, n.left, n.right, lctx, rctx
            )
            lk = (n.left, lctx, rm)
            rk = (n.right, lm, rctx)
            if not expanded:
                todo.append((node_id, lctx, rctx, True))
                if rk not in self.emit:
                    todo.append((n.right, lm, rctx, False))
                if lk not in self.emit:
                    todo.append((n.left, lctx, rm, False))
                continue
            self.emit[key] = self.A.cat(self.emit[lk], self.emit[rk])
        return self.emit[root]

    def apply(self, q: int) -> int:
        return self.block(q, self.B.left.start, self.B.right.start)


def main() -> None:
    B = lazy_from_eager(build_step(10))
    A = SLP()
    seed = repair_build(A, encode(1, (7, 18), 10))
    # actual 196 pair half is parity 1, [7,18] for pair full [7,18,7]
    assert decode(A.materialize(seed), 10) == (1, (7, 18))
    T = BimachineSLP(B, A)
    rows = []
    q = seed
    _rng = random.Random(196)
    for step in range(1, 257):
        t = time.perf_counter()
        q = T.apply(q)
        dt = time.perf_counter() - t
        if step <= 64:
            p, h = decode(A.materialize(q), 10)
            pp = 1
            hh: tuple[int, ...] = (7, 18)
            for _ in range(step):
                pp, hh = ref(pp, hh, 10)
            assert (p, h) == (pp, hh)
        if step in (1, 2, 4, 8, 16, 32, 64, 128, 256):
            m: dict[str, int | float] = dict(A.metrics(q))
            m.update(
                step=step,
                seconds=dt,
                total_arena_nodes=len(A.nodes),
                memo_blocks=len(T.emit),
                memo_forward=len(T.fwd),
                memo_reverse=len(T.rev),
            )
            rows.append(m)
            print(m, flush=True)
    (
        report_output(
            "devtools.verification.builders.slp_cascade", "slp_cascade_metrics.json"
        )
    ).write_text(json.dumps(rows, indent=2))
    lines = [
        "# Compressed-word cascade evaluation",
        "",
        "Exact one-step bimachine evaluation over a hash-consed SLP; no input word is materialized during the transform.",
        "",
        "|steps|word length|reachable SLP nodes|arena nodes|block-section memo|last step sec|",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for r in rows:
        lines.append(
            f"|{r['step']}|{r['length']}|{r['nodes']}|{r['total_arena_nodes']}|{r['memo_blocks']}|{r['seconds']:.6f}|"
        )
    lines += [
        "",
        "This is an exact spatial cascade/section engine.  It removes per-digit scans when repeated SLP blocks exist, but sequentially applying the one-step operator is still linear in temporal step count; a powered section rewrite is required for full J.",
    ]
    (
        report_output(
            "devtools.verification.builders.slp_cascade", "SLP_CASCADE_RESULTS.md"
        )
    ).write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
