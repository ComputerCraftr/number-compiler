"""Research-only encoding analyses for an already exact finite prime field.

This module deliberately sits outside :mod:`prime_coordinates`: the production
prime projector retains pair/wheel/hyperbolic carriers only.  Higher-radix MDD,
Zeckendorf, and period experiments consume exact prime lanes but are never on a
primality execution path.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.contracts.iterative_queries import (
    defer_binary_level,
)
from number_compiler.arithmetic.functions.decision import intern_binary_decision
from number_compiler.sequences.prime.radix import (
    commutative_cache_pair,
    progression_decision,
)
from number_compiler.sequences.prime.set import (
    canonical_multiplicative_lanes,
    finite_cover_lanes,
)


class _PowerRadixMDD:
    __slots__ = ("nodes", "or_cache", "or_calls", "radix", "unique", "width")

    def __init__(self, radix: int, width: int) -> None:
        self.radix = int(radix)
        self.width = int(width)
        self.nodes: dict[int, tuple[int, tuple[int, ...]] | None] = {0: None, 1: None}
        self.unique: dict[tuple[int, tuple[int, ...]], int] = {}
        self.or_cache: dict[tuple[int, int], int] = {}
        self.or_calls = 0

    def mk(self, var: int, children: Sequence[int]) -> int:
        children = tuple(map(int, children))
        if len(children) != self.radix:
            raise ValueError(len(children))
        if all(child == children[0] for child in children):
            return children[0]
        key = (int(var), children)
        old = self.unique.get(key)
        if old is not None:
            return old
        node = len(self.nodes)
        self.nodes[node] = key
        self.unique[key] = node
        return node

    def progression(self, factor: int, phase: int, first: int) -> int:
        return progression_decision(
            self.width, self.radix, factor, phase, first, self.mk
        )

    def or_(self, a: int, b: int) -> int:
        root = (int(a), int(b))
        memo: dict[tuple[int, int], int] = {}
        stack: list[tuple[int, int, bool]] = [(root[0], root[1], False)]
        while stack:
            x, y, expanded = stack.pop()
            if not expanded:
                self.or_calls += 1
            key_xy = (x, y)
            if key_xy in memo:
                continue
            if x == 1 or y == 1:
                memo[key_xy] = 1
                continue
            if x == 0:
                memo[key_xy] = y
                continue
            if y == 0 or x == y:
                memo[key_xy] = x
                continue
            aa, bb, cached = commutative_cache_pair(x, y, self.or_cache)
            cache_key = aa, bb
            if cached is not None:
                memo[key_xy] = cached
                continue
            na, nb = self.nodes[aa], self.nodes[bb]
            if na is None or nb is None:
                raise AssertionError((aa, bb))
            va, ca = na
            vb, cb = nb
            var = max(va, vb)
            if va != var:
                ca = (aa,) * self.radix
            if vb != var:
                cb = (bb,) * self.radix
            child_keys = tuple(zip(ca, cb))
            if not expanded:
                stack.append((x, y, True))
                for cx, cy in reversed(child_keys):
                    stack.append((cx, cy, False))
                continue
            out = self.mk(var, tuple(memo[pair] for pair in child_keys))
            self.or_cache[cache_key] = out
            memo[key_xy] = out
        return memo[root]

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
            _var, children = item
            stack.extend(children)
        return len(seen)


@dataclass(frozen=True, slots=True)
class PowerRadixPrimeMetrics:
    start: int
    length: int
    radix: int
    digits: int
    periodic_lanes: int
    finite_lanes: int
    reachable_nodes: int
    reachable_child_refs: int
    allocated_nodes: int
    allocated_child_refs: int
    cached_or_pairs: int
    or_calls: int


def project_prime_power_radix_metrics(
    start: int,
    length: int,
    radix: int,
    *,
    finite_cover: bool = True,
) -> PowerRadixPrimeMetrics:
    """Compile factor progressions directly into an r-ary reduced decision DAG.

    ``length`` must be an exact power of ``radix``.  Child references, not just
    node identities, are metered so high-arity nodes cannot fake compression.
    """
    start, length, radix = int(start), int(length), int(radix)
    if start < 3 or start % 2 == 0 or length <= 0 or radix < 2:
        raise ValueError((start, length, radix))
    width = 0
    remaining = length
    while remaining > 1 and remaining % radix == 0:
        remaining //= radix
        width += 1
    if remaining != 1:
        raise ValueError("length must be an exact positive power of radix")
    _candidates, _natural, periodic = canonical_multiplicative_lanes(start, length)
    lanes = finite_cover_lanes(start, length) if finite_cover else periodic
    arena = _PowerRadixMDD(radix, width)
    root = 0
    for lane in lanes:
        root = arena.or_(
            root, arena.progression(lane.factor, lane.phase, lane.first_index)
        )
    reachable = arena.reachable_nodes(root)
    allocated = len(arena.nodes) - 2
    return PowerRadixPrimeMetrics(
        start,
        length,
        radix,
        width,
        len(periodic),
        len(lanes),
        reachable,
        reachable * radix,
        allocated,
        allocated * radix,
        len(arena.or_cache),
        arena.or_calls,
    )


def zeckendorf_weights(max_value: int) -> tuple[int, ...]:
    max_value = int(max_value)
    if max_value < 0:
        raise ValueError(max_value)
    weights = [1, 2]
    while weights[-1] <= max_value:
        weights.append(weights[-1] + weights[-2])
    if weights[-1] > max_value and len(weights) > 1:
        weights.pop()
    return tuple(weights) if weights else (1,)


def zeckendorf_digits(
    value: int, weights: Sequence[int] | None = None
) -> tuple[int, ...]:
    value = int(value)
    if value < 0:
        raise ValueError(value)
    if weights is None:
        weights = zeckendorf_weights(value)
    weights = tuple(map(int, weights))
    remaining = value
    bits = [0] * len(weights)
    for i in range(len(weights) - 1, -1, -1):
        if weights[i] <= remaining:
            bits[i] = 1
            remaining -= weights[i]
    if remaining or any(bits[i] and bits[i + 1] for i in range(len(bits) - 1)):
        raise AssertionError((value, weights, bits, remaining))
    return tuple(bits)


@dataclass(frozen=True, slots=True)
class ZeckendorfDecisionMetrics:
    length: int
    digits: int
    order: str
    nonterminal_nodes: int
    child_refs: int


def zeckendorf_bitmap_decision_metrics(
    mask: int,
    length: int,
    *,
    order: str = "msb",
) -> ZeckendorfDecisionMetrics:
    """Reduce a finite bitmap over the exact Zeckendorf code domain.

    Missing edges are explicit domain information, so Fibonacci's sparse code
    space is not treated as free don't-care input.
    """
    mask, length = int(mask), int(length)
    if length <= 0 or mask < 0 or mask >= (1 << length) or order not in ("lsb", "msb"):
        raise ValueError((mask, length, order))
    weights = zeckendorf_weights(length - 1)
    codes = tuple(zeckendorf_digits(j, weights) for j in range(length))
    positions = (
        tuple(range(len(weights)))
        if order == "lsb"
        else tuple(range(len(weights) - 1, -1, -1))
    )
    # terminal ids: -1 = absent/invalid code, 0/1 = output bits.
    unique: dict[tuple[int, int, int], int] = {}
    rows = tuple((code, (mask >> j) & 1) for j, code in enumerate(codes))

    root_key = (rows, 0)
    memo: dict[tuple[tuple[tuple[tuple[int, ...], int], ...], int], int] = {}
    stack: list[tuple[tuple[tuple[tuple[int, ...], int], ...], int, bool]] = [
        (rows, 0, False)
    ]
    while stack:
        subrows, level, expanded = stack.pop()
        state = (subrows, level)
        if state in memo:
            continue
        if not subrows:
            memo[state] = -1
            continue
        if level == len(positions):
            outputs = {out for _code, out in subrows}
            if len(outputs) != 1:
                raise AssertionError(outputs)
            memo[state] = next(iter(outputs))
            continue
        pos = positions[level]
        low = tuple(row for row in subrows if row[0][pos] == 0)
        high = tuple(row for row in subrows if row[0][pos] == 1)
        if not expanded:
            defer_binary_level(stack, subrows, level, low, high, memo)
            continue
        lo, hi = memo[low, level + 1], memo[high, level + 1]
        old = intern_binary_decision(unique, pos, lo, hi)
        memo[state] = old
    _root = memo[root_key]
    return ZeckendorfDecisionMetrics(
        length, len(weights), order, len(unique), 2 * len(unique)
    )


def signed_multiplicative_order(base: int, modulus: int) -> tuple[int, int]:
    """Smallest k with ``base**k == +/-1 (mod modulus)`` and its sign."""
    base, modulus = int(base), int(modulus)
    if modulus <= 1 or gcd(base, modulus) != 1:
        raise ValueError((base, modulus))
    value = 1
    for k in range(1, modulus):
        value = (value * base) % modulus
        if value == 1:
            return k, 1
        if value == modulus - 1:
            return k, -1
    raise AssertionError((base, modulus))


def pisano_period(modulus: int) -> int:
    modulus = int(modulus)
    if modulus <= 1:
        raise ValueError(modulus)
    a, b = 0, 1
    # For prime factors used by the projector the period is <= 2(q+1) when
    # q == +/-2 mod 5 and divides q-1 otherwise; 6q is a safe research bound.
    for k in range(1, 6 * modulus + 7):
        a, b = b, (a + b) % modulus
        if a == 0 and b == 1:
            return k
    raise AssertionError(modulus)


@dataclass(frozen=True, slots=True)
class FactorCoordinatePeriodMetrics:
    base: int
    lane_count: int
    signed_order_sum: int
    signed_order_max: int
    distinct_signed_orders: int
    pisano_sum: int
    pisano_max: int
    distinct_pisano_periods: int


def factor_coordinate_period_metrics(
    start: int, length: int, *, base: int = 2
) -> FactorCoordinatePeriodMetrics:
    """Compare packed-radix folding periods with Fibonacci/Pisano periods."""
    start, length, base = int(start), int(length), int(base)
    _candidates, _natural, lanes = canonical_multiplicative_lanes(start, length)
    factors = tuple(lane.factor for lane in lanes if gcd(base, lane.factor) == 1)
    orders = tuple(signed_multiplicative_order(base, q)[0] for q in factors)
    pisanos = tuple(pisano_period(q) for q in factors)
    return FactorCoordinatePeriodMetrics(
        base,
        len(factors),
        sum(orders),
        max(orders, default=0),
        len(set(orders)),
        sum(pisanos),
        max(pisanos, default=0),
        len(set(pisanos)),
    )


__all__ = [
    "FactorCoordinatePeriodMetrics",
    "PowerRadixPrimeMetrics",
    "ZeckendorfDecisionMetrics",
    "factor_coordinate_period_metrics",
    "pisano_period",
    "project_prime_power_radix_metrics",
    "signed_multiplicative_order",
    "zeckendorf_bitmap_decision_metrics",
    "zeckendorf_digits",
    "zeckendorf_weights",
]
