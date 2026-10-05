from __future__ import annotations

import json
import time
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

from devtools.paths import report_output
from devtools.verification.oracles.sequence_arithmetic import reference_successor
from devtools.verification.sequence_reduction import balanced_reduce
from number_compiler.arithmetic.carry.carry_labels import (
    IDENTITY as I,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ONE as R1,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ZERO as R0,
)
from number_compiler.arithmetic.formula.summary import BlockSummary, compose_summaries
from number_compiler.arithmetic.formula.types import RadixSpec

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


@dataclass(frozen=True, slots=True)
class Node:
    id: int
    length: int
    value: int | None
    left: int | None
    right: int | None
    summary: BlockSummary
    first: int
    last: int


DEFAULT_SPEC = RadixSpec(10)


class Arena:
    def __init__(self, spec: RadixSpec = DEFAULT_SPEC) -> None:
        self.spec = spec
        self.nodes: list[Node] = []
        self.intern: dict[tuple[str, int] | tuple[str, int, int], int] = {}
        self.step_cache: dict[tuple[int, int, int, int, int, bool], int] = {}

    def leaf(self, v: int) -> int:
        v = int(v)
        t = self.spec.threshold
        sign = 0 if v == t else (1 if v > t else -1)
        s = BlockSummary(
            1,
            sign == 0,
            None if sign == 0 else 0,
            None if sign == 0 else 0,
            sign,
            sign,
            I if sign == 0 else (R1 if sign > 0 else R0),
        )
        k = ("L", v)
        q = self.intern.get(k)
        if q is None:
            q = len(self.nodes)
            self.intern[k] = q
            self.nodes.append(Node(q, 1, v, None, None, s, v, v))
        return q

    def cat(self, a: int, b: int) -> int:
        A, B = self.nodes[a], self.nodes[b]
        k = ("C", a, b)
        q = self.intern.get(k)
        if q is None:
            s = compose_summaries(A.summary, B.summary)
            q = len(self.nodes)
            self.intern[k] = q
            self.nodes.append(
                Node(q, A.length + B.length, None, a, b, s, A.first, B.last)
            )
        return q

    def build(self, vals: Sequence[int]) -> int:
        q = [self.leaf(v) for v in vals]
        return balanced_reduce(q, self.cat)

    @staticmethod
    def apply_transfer(s: BlockSummary, c: int) -> int:
        if s.transfer == I:
            return c
        return int(s.transfer == R1)

    @staticmethod
    def apply_reverse(s: BlockSummary, c: int) -> int:
        if s.all_threshold:
            return c
        return int(s.first_reset_sign > 0)

    def transform(
        self,
        q: int,
        g: int,
        left_state: int = 0,
        r: int = 0,
        prev: int | None = None,
        global_first: bool = True,
    ) -> int:
        root = (
            q,
            int(g),
            int(left_state),
            int(r),
            -1 if prev is None else int(prev),
            bool(global_first),
        )
        todo = [(q, int(g), int(left_state), int(r), prev, bool(global_first), False)]
        while todo:
            node_id, grow, lctx, rctx, prior, is_first, expanded = todo.pop()
            key = (
                node_id,
                grow,
                lctx,
                rctx,
                -1 if prior is None else int(prior),
                is_first,
            )
            if key in self.step_cache:
                continue
            n = self.nodes[node_id]
            base = self.spec.base
            t = base - 1
            if n.value is not None:
                val = n.value
                l1 = 0 if val < t else (lctx if val == t else 1)
                ri = 0 if val < t else (rctx if val == t else 1)
                if not grow:
                    y = 2 * val + lctx + rctx - base * (l1 + ri)
                elif is_first:
                    y = val + 1 - base * l1
                else:
                    assert prior is not None
                    rim1 = 0 if prior < t else (ri if prior == t else 1)
                    y = val + prior + lctx + ri - base * (l1 + rim1)
                if not 0 <= y <= 2 * (base - 1):
                    raise AssertionError((val, grow, lctx, rctx, prior, y))
                self.step_cache[key] = self.leaf(y)
                continue
            assert n.left is not None and n.right is not None
            L, R = self.nodes[n.left], self.nodes[n.right]
            lmid = self.apply_transfer(L.summary, lctx)
            rmid = self.apply_reverse(R.summary, rctx)
            lk = (
                n.left,
                grow,
                lctx,
                rmid,
                -1 if prior is None else int(prior),
                is_first,
            )
            rk = (n.right, grow, lmid, rctx, int(L.last), False)
            if not expanded:
                todo.append((node_id, grow, lctx, rctx, prior, is_first, True))
                if rk not in self.step_cache:
                    todo.append((n.right, grow, lmid, rctx, L.last, False, False))
                if lk not in self.step_cache:
                    todo.append((n.left, grow, lctx, rmid, prior, is_first, False))
                continue
            self.step_cache[key] = self.cat(self.step_cache[lk], self.step_cache[rk])
        return self.step_cache[root]

    def successor(self, q: int) -> tuple[int, int]:
        n = self.nodes[q]
        g = int((not n.summary.all_threshold) and n.summary.first_reset_sign > 0)
        core = self.transform(q, g, 0, 0, None, True)
        if g:
            # symmetric new outer coefficient equals the first output coefficient.
            core = self.cat(core, self.leaf(self.nodes[core].first))
        return core, g

    def materialize(self, q: int) -> tuple[int, ...]:
        out = []
        st = [q]
        while st:
            z = st.pop()
            n = self.nodes[z]
            if n.value is not None:
                out.append(n.value)
            else:
                assert n.left is not None and n.right is not None
                st.append(n.right)
                st.append(n.left)
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
            if n.value is None:
                assert n.left is not None and n.right is not None
                st.extend((n.left, n.right))
        return seen


def reference(full: tuple[int, ...], b: int = 10) -> tuple[tuple[int, ...], int]:
    result = reference_successor(full, b)
    return result, len(result) - len(full)


def main() -> None:
    A = Arena()
    q = A.build((7, 18, 7))
    vals: tuple[int, ...] = (7, 18, 7)
    rows = []
    t0 = time.perf_counter()
    for n in range(1, 2049):
        q, g = A.successor(q)
        vals2, g2 = reference(vals)
        assert g == g2
        if n <= 256:
            assert A.materialize(q) == vals2
        vals = vals2
        if n in (64, 128, 256, 512, 1024, 2048):
            r = {
                "step": n,
                "width": A.nodes[q].length,
                "reachable_nodes": len(A.reachable(q)),
                "arena_nodes": len(A.nodes),
                "section_cache": len(A.step_cache),
                "elapsed": time.perf_counter() - t0,
            }
            rows.append(r)
            print(r, flush=True)
    (
        report_output(
            "devtools.verification.builders.symmetric_block_cascade",
            "symmetric_block_cascade_metrics.json",
        )
    ).write_text(json.dumps(rows, indent=2))
    (
        report_output(
            "devtools.verification.builders.symmetric_block_cascade",
            "SYMMETRIC_BLOCK_CASCADE_RESULTS.md",
        )
    ).write_text(
        "# Symmetric BlockSummary cascade\n\n"
        + "".join(
            f"- n={r['step']}: width {r['width']}, reachable nodes {r['reachable_nodes']}, arena {r['arena_nodes']}, cached sections {r['section_cache']}\n"
            for r in rows
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
