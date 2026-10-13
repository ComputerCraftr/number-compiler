"""Projection adapter for exact indexed prime selection."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.elementary_payloads import ScalarTermPayload
from number_compiler.api.number_api import ProjectedNumberTerm, ProjectionMetrics
from number_compiler.api.symbolic_terms import SymbolicExpression

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import PrimeTermQuery


def project(compiler: NumberCompiler, query: PrimeTermQuery) -> ProjectedNumberTerm:
    from number_compiler.sequences.prime.select import nth_prime_at_or_after

    value, metrics = nth_prime_at_or_after(
        query.start,
        query.index,
        max_states=query.max_prime_states,
        max_work=query.max_prime_work,
        max_stages=query.max_prime_stages,
        shared_cache=compiler._shared_cache,
    )
    return ProjectedNumberTerm(
        "prime",
        query.index,
        query.start,
        None,
        SymbolicExpression("prime", query.index, query.start),
        ScalarTermPayload(value),
        ProjectionMetrics(
            "prime",
            query.index,
            metrics.descent_rounds + metrics.expansion_rounds,
            metrics.projection_work,
            1,
            max(1, value.bit_length()),
            1,
            prime_block_compilations=metrics.block_compilations,
            prime_max_block_length=metrics.max_block_length,
            prime_dag_states=metrics.dag_states,
            prime_cache_hits=metrics.cache_hits,
            prime_factor_stages=metrics.factor_stages,
            prime_discovery_queries=metrics.discovery_queries,
            prime_peak_pending_frames=metrics.peak_pending_frames,
            prime_retained_entries=metrics.retained_entries,
            prime_arithmetic_bit_work=metrics.arithmetic_bit_work,
            prime_parent_gap_positions_materialized=(
                metrics.parent_gap_positions_materialized
            ),
            shared_cache_hits=metrics.shared_cache_hits,
            shared_cache_misses=metrics.shared_cache_misses,
            shared_cache_entries=metrics.shared_cache_entries,
            shared_cache_bytes=metrics.shared_cache_bytes,
            shared_cache_evictions=metrics.shared_cache_evictions,
            shared_cache_bypasses=metrics.shared_cache_bypasses,
            shared_cache_publications=metrics.shared_cache_publications,
            prime_admission_work=metrics.admission_work,
            prime_request_allocations=metrics.request_allocations,
            prime_scheduler_work=metrics.scheduler_work,
            prime_scheduler_peak_entries=metrics.scheduler_allocations,
            prime_scheduler_counters=metrics.scheduler_counters,
        ),
    )
