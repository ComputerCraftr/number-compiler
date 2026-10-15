"""Projection adapter for powered physical Collatz terms."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.number_api import (
    PoweredCollatzTermPayload,
    ProjectedNumberTerm,
    ProjectionMetrics,
)
from number_compiler.api.observation_types import FamilyId
from number_compiler.api.symbolic_terms import SymbolicExpression
from number_compiler.arithmetic.fields.radix import bit_width

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import CollatzTermQuery


def project(compiler: NumberCompiler, query: CollatzTermQuery) -> ProjectedNumberTerm:
    from number_compiler.api.query_types import CollatzTermQuery
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    def valid(owner: PoweredCollatzTerm) -> bool:
        return (
            (owner.seed, owner.steps) == (query.seed, query.index)
            and owner._shared_cache is compiler._shared_cache
            and owner._max_context_nodes == compiler._max_context_nodes
            and owner._max_cache_entries == compiler._max_cache_entries
            and owner._ledger.max_nodes == compiler._max_context_nodes
            and owner._ledger.max_cache_entries == compiler._max_cache_entries
        )

    # Radix is a demand-time view, not part of the binary source owner key.
    term = compiler._powered_term(
        (CollatzTermQuery, query.seed, query.index),
        PoweredCollatzTerm,
        lambda: PoweredCollatzTerm(
            query.seed,
            query.index,
            shared_cache=compiler._shared_cache,
            max_context_nodes=compiler._max_context_nodes,
            max_cache_entries=compiler._max_cache_entries,
        ),
        valid,
    )
    node_bits = bit_width(max(1, term.operator_nodes))
    descriptor_bits = term.descriptor_bits + term.operator_nodes * max(1, node_bits + 2)
    return ProjectedNumberTerm(
        FamilyId.COLLATZ,
        query.index,
        query.seed,
        query.radix,
        SymbolicExpression(FamilyId.COLLATZ, query.index, query.seed),
        PoweredCollatzTermPayload(term, query.radix),
        ProjectionMetrics(
            FamilyId.COLLATZ,
            query.index,
            term.compose_operations,
            0,
            max(1, term.operator_nodes),
            descriptor_bits,
            term.maximum_width,
        ),
    )
