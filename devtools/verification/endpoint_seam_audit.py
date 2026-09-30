"""Exact endpoint seam experiments with explicit first-use work accounting.

This is a bounded research evaluator, not a production jump certificate.
Canonical endpoints erase predecessor provenance. Discovering a cold endpoint
still invokes the supplied primitive and materializes its intermediate values.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable, Hashable, Iterable
from typing import Generic, TypeVar

T = TypeVar("T", bound=Hashable)


def audit_endpoint_frontier(
    sources: Iterable[T],
    step: Callable[[T], T],
    *,
    horizons: tuple[int, ...] = (1, 2, 4, 8, 16, 32),
    spatial_size: Callable[[T], int] | None = None,
    max_sources: int = 200_000,
) -> dict[str, object]:
    """Push a counted corpus through canonical exact endpoint frontiers.

    Source multiplicities survive a merge, but transitions execute only once
    per distinct current endpoint. Hits count actual equal-key publications.
    Future congruence follows from exact endpoint identity; this routine does
    not label a feature-key comparison as a separate measured closure proof.
    """
    if not horizons or any(type(n) is not int or n <= 0 for n in horizons):
        raise ValueError("positive exact horizons required")
    if max(horizons) > 1024 or max_sources <= 0:
        raise ValueError("bounded endpoint audit budget exceeded")
    frontier: Counter[T] = Counter()
    source_count = 0
    for source in sources:
        source_count += 1
        if source_count > max_sources:
            raise ValueError("endpoint source corpus budget exceeded")
        frontier[source] += 1
    distinct_sources = len(frontier)
    primitive = hits = positions = 0
    rows: list[dict[str, int]] = []
    for duration in range(1, max(horizons) + 1):
        following: Counter[T] = Counter()
        for source, multiplicity in frontier.items():
            primitive += 1
            if spatial_size is not None:
                positions += spatial_size(source)
            target = step(source)
            if target in following:
                hits += 1
            following[target] += multiplicity
        frontier = following
        if duration in horizons:
            rows.append(
                {
                    "duration": duration,
                    "endpoint_classes": len(frontier),
                    "aliases": distinct_sources - len(frontier),
                    "max_fiber": max(frontier.values(), default=0),
                    "primitive_successors": primitive,
                    "endpoint_intern_hits": hits,
                    "source_position_visits": positions,
                }
            )
    return {
        "source_occurrences": source_count,
        "distinct_sources": distinct_sources,
        "rows": rows,
        "future_congruence_basis": "exact endpoint identity; deterministic-kernel theorem",
        "first_use_sublinear_certified": False,
        "intermediate_endpoints_materialized": primitive,
    }


class BoundedEndpointPowerArena(Generic[T]):
    """Bottom-up dyadic memoization whose values are canonical endpoints only.

    Both cache entries and primitive work have hard bounds. A populated cache
    can power with the primitive poisoned. A cold nonrepeating orbit still
    requires one primitive application per generation: the counters expose it.
    """

    def __init__(
        self,
        step: Callable[[T], T],
        *,
        max_entries: int = 100_000,
        max_primitives: int = 100_000,
    ) -> None:
        if max_entries <= 0 or max_primitives <= 0:
            raise ValueError("positive endpoint arena budgets required")
        self.step = step
        self.max_entries = max_entries
        self.max_primitives = max_primitives
        self._results: dict[tuple[int, T], T] = {}
        self._endpoints: dict[T, T] = {}
        self.primitive_successors = 0
        self.memo_hits = 0
        self.endpoint_intern_hits = 0
        self.power_requests = 0
        self.compositions = 0

    @property
    def retained_results(self) -> int:
        return len(self._results)

    @property
    def retained_endpoints(self) -> int:
        return len(self._endpoints)

    def _publish(self, key: tuple[int, T], target: T) -> None:
        if len(self._results) >= self.max_entries:
            raise ValueError("endpoint result budget exceeded")
        if target in self._endpoints:
            self.endpoint_intern_hits += 1
            target = self._endpoints[target]
        else:
            if len(self._endpoints) >= self.max_entries:
                raise ValueError("endpoint payload budget exceeded")
            self._endpoints[target] = target
        self._results[key] = target

    def power(self, source: T, level: int) -> T:
        """Return step^(2^level)(source), charging any missing primitive work."""
        if type(level) is not int or not 0 <= level <= 64:
            raise ValueError("dyadic level outside bounded audit range")
        self.power_requests += 1
        stack = [(level, source)]
        while stack:
            key = stack[-1]
            if key in self._results:
                self.memo_hits += 1
                stack.pop()
                continue
            depth, current = key
            if depth == 0:
                if self.primitive_successors >= self.max_primitives:
                    raise ValueError("endpoint primitive budget exceeded")
                self.primitive_successors += 1
                self._publish(key, self.step(current))
                stack.pop()
                continue
            first = (depth - 1, current)
            if first not in self._results:
                stack.append(first)
                continue
            self.memo_hits += 1
            midpoint = self._results[first]
            second = (depth - 1, midpoint)
            if second not in self._results:
                stack.append(second)
                continue
            self.memo_hits += 1
            self.compositions += 1
            self._publish(key, self._results[second])
            stack.pop()
        return self._results[(level, source)]
