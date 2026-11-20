"""Projection adapter for the bounded exact 2rev10 source grammar."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.number_api import ProjectedNumberTerm, ProjectionMetrics
from number_compiler.api.projections.decimal_reversal import matches_bounded_query
from number_compiler.api.reverse_payloads import DoubleReverseTermPayload
from number_compiler.api.symbolic_terms import SymbolicExpression
from number_compiler.arithmetic.contracts.family_identity import FamilyId

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import DoubleReverseTermQuery


def project(
    compiler: NumberCompiler, query: DoubleReverseTermQuery
) -> ProjectedNumberTerm:
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm

    term = compiler.powered_term(
        query,
        DoubleReverseTerm,
        lambda: DoubleReverseTerm(
            query.seed,
            query.index,
            max_steps=query.max_steps,
            max_state_bits=query.max_state_bits,
            max_context_nodes=compiler.max_context_nodes,
            max_cache_entries=compiler.max_cache_entries,
        ),
        lambda owner: matches_bounded_query(owner, query, compiler),
    )
    return ProjectedNumberTerm(
        FamilyId.DOUBLE_REVERSE,
        query.index,
        query.seed,
        10,
        SymbolicExpression(FamilyId.DOUBLE_REVERSE, query.index, query.seed, 10),
        DoubleReverseTermPayload(term),
        ProjectionMetrics(
            FamilyId.DOUBLE_REVERSE,
            query.index,
            0,
            0,
            1,
            query.seed.bit_length() + query.index.bit_length(),
            None,
        ),
    )
