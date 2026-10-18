"""Demanded metrics projection for one powered Collatz term."""

from __future__ import annotations

from number_compiler.resources.collatz_power_metrics import (
    CollatzPhysicalBlockMetrics,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_unindexed_metrics
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.powered_metrics import project_powered_metrics


def project_collatz_term_metrics(
    ledger: ResourceLedger,
    *,
    seed: int,
    steps: int,
    operator_nodes: int,
    compose_operations: int,
    syntax_depth_bound: int,
    descriptor_bits: int,
) -> CollatzPhysicalBlockMetrics:
    """Read existing counters without causing another source observation."""
    point = collect_unindexed_metrics(ledger)
    return project_powered_metrics(
        CollatzPhysicalBlockMetrics,
        point,
        seed=seed,
        steps=steps,
        operator_nodes=operator_nodes,
        compose_operations=compose_operations,
        syntax_depth_bound=syntax_depth_bound,
        descriptor_bits=descriptor_bits,
        direct_powered_point_queries=ledger.counters.get(
            _collatz_keys.DIRECT_POWERED_POINT_QUERIES, 0
        ),
        collatz_physical_factored_output_compilations=(
            point.resource_work_counters.get(
                _collatz_keys.COLLATZ_PHYSICAL_FACTORED_OUTPUT_COMPILATIONS, 0
            )
        ),
        collatz_physical_joint_output_tables_elided=(
            point.resource_work_counters.get(
                _collatz_keys.COLLATZ_PHYSICAL_JOINT_OUTPUT_TABLES_ELIDED, 0
            )
        ),
    )


__all__ = ("project_collatz_term_metrics",)
