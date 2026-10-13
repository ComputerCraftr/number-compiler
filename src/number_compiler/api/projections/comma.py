"""Projection adapter for the certified A367620 comma sequence."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.api.number_api import ProjectedNumberTerm, ProjectionMetrics
from number_compiler.api.symbolic_terms import SymbolicExpression

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import CommaTermQuery


def project(compiler: NumberCompiler, query: CommaTermQuery) -> ProjectedNumberTerm:
    from number_compiler.sequences.comma.certificates import CERTIFICATE_ID
    from number_compiler.sequences.comma.power import CommaTerm

    context_nodes = (
        query.max_comma_states
        if compiler._max_context_nodes is None
        else min(query.max_comma_states, compiler._max_context_nodes)
    )
    cache_entries = (
        query.max_comma_states
        if compiler._max_cache_entries is None
        else min(query.max_comma_states, compiler._max_cache_entries)
    )

    def valid(owner: CommaTerm) -> bool:
        return (
            owner.index == query.index
            and owner.max_states == query.max_comma_states
            and owner.max_work == query.max_comma_work
            and owner.certificate_version == CERTIFICATE_ID
            and owner.shared_cache is compiler._shared_cache
            and owner.ledger.max_nodes == context_nodes
            and owner.ledger.max_cache_entries == cache_entries
        )

    term = compiler._powered_term(
        (query, CERTIFICATE_ID),
        CommaTerm,
        lambda: CommaTerm(
            query.index,
            max_states=query.max_comma_states,
            max_work=query.max_comma_work,
            certificate_version=CERTIFICATE_ID,
            shared_cache=compiler._shared_cache,
            max_context_nodes=compiler._max_context_nodes,
            max_cache_entries=compiler._max_cache_entries,
        ),
        valid,
    )
    return ProjectedNumberTerm(
        "a367620",
        query.index,
        20,
        10,
        SymbolicExpression("a367620", query.index),
        CommaTermPayload(term),
        ProjectionMetrics(
            "a367620",
            query.index,
            0,
            0,
            1,
            query.index.bit_length() + 5,
            None,
        ),
    )
