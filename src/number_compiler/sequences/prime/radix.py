"""Direct radix decision-DAG projection of multiplicative prime lanes.

Unlike :mod:`number_compiler.projection.radix_decision`, this path does not first materialize a
length-bit composite bitmap.  Each canonical arithmetic-progression factor lane
is compiled directly into a reduced binary decision DAG over the candidate
index bits, then the lanes are OR-composed with early hash-consing.  Count and
first-hole are derived from the final DAG.

The experiment is exact but deliberately metered: intermediate BDD nodes and OR
applications are reported.  At current scales the final DAG is compact, while
construction work is still larger than the irreducible factor-lane basis.
"""

from __future__ import annotations
from number_compiler.arithmetic.contracts.iterative_queries import (
    defer_indexed_dependencies,
)

from dataclasses import dataclass
from collections.abc import Callable

from number_compiler.sequences.prime.set import (
    PrimeBlockSummary,
    canonical_multiplicative_lanes,
)


def commutative_cache_pair(
    first: int, second: int, cache: dict[tuple[int, int], int]
) -> tuple[int, int, int | None]:
    low, high = (first, second) if first <= second else (second, first)
    return low, high, cache.get((low, high))


def progression_decision(
    width: int,
    radix: int,
    factor: int,
    phase: int,
    first: int,
    make_node: Callable[[int, tuple[int, ...]], int],
) -> int:
    """Compile one arithmetic progression into an ordered radix decision DAG."""
    factor, phase, first = map(int, (factor, phase, first))
    root = (width - 1, 0, radix**width)
    memo: dict[tuple[int, int, int], int] = {}
    stack: list[tuple[int, int, int, bool]] = [(*root, False)]
    while stack:
        variable, start, size, ready = stack.pop()
        key = variable, start, size
        if key in memo:
            continue
        lower = max(start, first)
        hit = lower + ((phase - lower) % factor)
        if hit >= start + size:
            memo[key] = 0
            continue
        if variable < 0:
            memo[key] = 1
            continue
        child_size = size // radix
        children = tuple(
            (variable - 1, start + digit * child_size, child_size)
            for digit in range(radix)
        )
        if not ready:
            stack.append((*key, True))
            stack.extend((*child, False) for child in reversed(children))
            continue
        memo[key] = make_node(variable, tuple(memo[child] for child in children))
    return memo[root]


class _BDD:
    __slots__ = ("nodes", "or_cache", "or_calls", "unique", "width")

    def __init__(self, width: int) -> None:
        self.width = int(width)
        self.nodes: dict[int, tuple[int, int, int] | None] = {0: None, 1: None}
        self.unique: dict[tuple[int, int, int], int] = {}
        self.or_cache: dict[tuple[int, int], int] = {}
        self.or_calls = 0

    def mk(self, var: int, low: int, high: int) -> int:
        if low == high:
            return low
        key = (int(var), int(low), int(high))
        old = self.unique.get(key)
        if old is not None:
            return old
        node = len(self.nodes)
        self.nodes[node] = key
        self.unique[key] = node
        return node

    def progression(self, factor: int, phase: int, first: int) -> int:
        return progression_decision(
            self.width,
            2,
            factor,
            phase,
            first,
            lambda variable, children: self.mk(variable, children[0], children[1]),
        )

    def or_(self, a: int, b: int) -> int:
        root = (int(a), int(b))
        results: dict[tuple[int, int], int] = {}
        stack: list[tuple[int, int, bool]] = [(root[0], root[1], False)]
        while stack:
            x, y, expanded = stack.pop()
            if not expanded:
                self.or_calls += 1
            if x == 1 or y == 1:
                results[(x, y)] = 1
                continue
            if x == 0:
                results[(x, y)] = y
                continue
            if y == 0 or x == y:
                results[(x, y)] = x
                continue
            a1, b1, cached = commutative_cache_pair(x, y, self.or_cache)
            key = a1, b1
            if cached is not None:
                results[(x, y)] = cached
                continue
            na = self.nodes[a1]
            nb = self.nodes[b1]
            if na is None or nb is None:
                raise AssertionError((a1, b1))
            va, la, ha = na
            vb, lb, hb = nb
            var = max(va, vb)
            alo, ahi = (la, ha) if va == var else (a1, a1)
            blo, bhi = (lb, hb) if vb == var else (b1, b1)
            low_key, high_key = (alo, blo), (ahi, bhi)
            if not expanded:
                defer_indexed_dependencies(stack, x, y, (low_key, high_key), results)
                continue
            low = results[low_key]
            high = results[high_key]
            out = self.mk(var, low, high)
            self.or_cache[key] = out
            results[(x, y)] = out
        return results[root]

    def reachable_nodes(self, root: int) -> int:
        seen: set[int] = set()
        stack = [root]
        while stack:
            node = stack.pop()
            if node < 2 or node in seen:
                continue
            seen.add(node)
            item = self.nodes[node]
            if item is None:
                raise AssertionError(node)
            _var, low, high = item
            stack.extend((low, high))
        return len(seen)

    def _count_ones(self, node: int, next_var: int) -> int:
        root = (int(node), int(next_var))
        memo: dict[tuple[int, int], int] = {}
        stack: list[tuple[int, int, bool]] = [(root[0], root[1], False)]
        while stack:
            q, nv, expanded = stack.pop()
            key = (q, nv)
            if key in memo:
                continue
            if q == 0:
                memo[key] = 0
                continue
            if q == 1:
                memo[key] = 1 << (nv + 1)
                continue
            item = self.nodes[q]
            if item is None:
                raise AssertionError(q)
            var, low, high = item
            lk, hk = (low, var - 1), (high, var - 1)
            if not expanded:
                stack.append((q, nv, True))
                stack.append((high, var - 1, False))
                stack.append((low, var - 1, False))
                continue
            memo[key] = (memo[lk] + memo[hk]) << (nv - var)
        return memo[root]

    def _first_zero(self, node: int, next_var: int) -> int | None:
        q = int(node)
        offset = 0
        while True:
            if q == 0:
                return offset
            if q == 1:
                return None
            item = self.nodes[q]
            if item is None:
                raise AssertionError(q)
            var, low, high = item
            if self._count_ones(low, var - 1) < (1 << var):
                q = low
            else:
                offset += 1 << var
                q = high

    def prime_summary(self, root: int) -> PrimeBlockSummary:
        total = 1 << self.width
        composite = self._count_ones(root, self.width - 1)
        first = self._first_zero(root, self.width - 1)
        return PrimeBlockSummary(total, total - composite, first)


@dataclass(frozen=True, slots=True)
class PrimeRadixProjection:
    start: int
    length: int
    summary: PrimeBlockSummary
    natural_lanes: int
    canonical_lanes: int
    reachable_bdd_nodes: int
    allocated_bdd_nodes: int
    cached_or_pairs: int
    or_calls: int


def project_odd_prime_block_radix(start: int, length: int) -> PrimeRadixProjection:
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length <= 0 or length & (length - 1):
        raise ValueError(
            "start must be odd >=3 and length must be a positive power of two"
        )
    width = length.bit_length() - 1
    _factor_candidates, natural_lanes, lanes = canonical_multiplicative_lanes(
        start, length
    )
    arena = _BDD(width)
    root = 0
    for lane in lanes:
        lane_root = arena.progression(lane.factor, lane.phase, lane.first_index)
        root = arena.or_(root, lane_root)
    return PrimeRadixProjection(
        start=start,
        length=length,
        summary=arena.prime_summary(root),
        natural_lanes=natural_lanes,
        canonical_lanes=len(lanes),
        reachable_bdd_nodes=arena.reachable_nodes(root),
        allocated_bdd_nodes=len(arena.nodes) - 2,
        cached_or_pairs=len(arena.or_cache),
        or_calls=arena.or_calls,
    )


__all__ = ["PrimeRadixProjection", "project_odd_prime_block_radix"]
