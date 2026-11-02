"""Demanded exact prime value using the existing source-owned selector."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.query_types import PrimeTermQuery

if TYPE_CHECKING:
    from number_compiler.sequences.prime.select import PrimeRankSelectMetrics


def select(
    query: PrimeTermQuery, shared_cache: bool
) -> tuple[int, PrimeRankSelectMetrics]:
    """Forward the admitted source and budgets identically for both consumers."""
    from number_compiler.sequences.prime.select import nth_prime_at_or_after

    return nth_prime_at_or_after(
        query.start,
        query.index,
        max_states=query.max_prime_states,
        max_work=query.max_prime_work,
        max_stages=query.max_prime_stages,
        shared_cache=shared_cache,
    )


def value(query: PrimeTermQuery, shared_cache: bool) -> int:
    result, _metrics = select(query, shared_cache)
    return result
