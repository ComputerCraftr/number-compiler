"""Projection adapter for the powered decimal reverse/add family."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.number_api import (
    ProjectedNumberTerm,
    ProjectionMetrics,
)
from number_compiler.api.reverse_payloads import PoweredReverseAddTermPayload
from number_compiler.api.symbolic_terms import SymbolicExpression
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.sequences.reverse_add.extent import ReverseAddExtent

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import ReverseAddTermQuery


def project(
    compiler: NumberCompiler, query: ReverseAddTermQuery
) -> ProjectedNumberTerm:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    def valid(owner: ReverseAddPoweredTerm) -> bool:
        return (
            (owner.seed, owner.generation, owner.base)
            == (
                query.seed,
                query.index,
                query.base,
            )
            and owner.resource_ledger.max_nodes == compiler.max_context_nodes
            and owner.resource_ledger.max_cache_entries == compiler.max_cache_entries
        )

    term = compiler.powered_term(
        query,
        ReverseAddPoweredTerm,
        lambda: ReverseAddPoweredTerm(
            query.seed,
            query.index,
            base=query.base,
            max_context_nodes=compiler.max_context_nodes,
            max_cache_entries=compiler.max_cache_entries,
        ),
        valid,
    )
    node_bits = bit_width(max(1, term.operator_nodes))
    descriptor_bits = term.descriptor_bits + term.operator_nodes * max(1, node_bits + 2)
    return ProjectedNumberTerm(
        FamilyId.REVERSE_ADD,
        query.index,
        query.seed,
        query.base,
        SymbolicExpression(FamilyId.REVERSE_ADD, query.index, query.seed, query.base),
        PoweredReverseAddTermPayload(term),
        ProjectionMetrics(
            FamilyId.REVERSE_ADD,
            query.index,
            term.compose_operations,
            0,
            max(1, term.operator_nodes),
            descriptor_bits,
            ReverseAddExtent(query.seed, query.base, query.index),
        ),
    )
