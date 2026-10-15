"""Projection adapter for the pinned blank-source Antihydra recurrence."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.number_api import (
    AntihydraTermPayload,
    ProjectedNumberTerm,
    ProjectionMetrics,
)
from number_compiler.api.observation_types import FamilyId
from number_compiler.api.symbolic_terms import SymbolicExpression

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import AntihydraTermQuery


def project(compiler: NumberCompiler, query: AntihydraTermQuery) -> ProjectedNumberTerm:
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    cache_capacity = (
        8192 if compiler._max_cache_entries is None else compiler._max_cache_entries
    )

    def valid(owner: AntihydraArithmeticTerm) -> bool:
        return (
            (owner.requested, owner.max_steps, owner.max_state_bits)
            == (query.index, query.max_steps, query.max_state_bits)
            and owner.max_cache_entries == cache_capacity
            and owner.engine.capacity == cache_capacity
            and owner.engine.shared_cache is compiler._shared_cache
            and owner.ledger is owner.engine.ledger
            and owner.ledger.max_nodes == cache_capacity + 32
            and owner.ledger.max_cache_entries == cache_capacity
        )

    term = compiler._powered_term(
        query,
        AntihydraArithmeticTerm,
        lambda: AntihydraArithmeticTerm(
            query.index,
            max_steps=query.max_steps,
            max_state_bits=query.max_state_bits,
            max_cache_entries=cache_capacity,
            shared_cache=compiler._shared_cache,
        ),
        valid,
    )
    descriptor_bits = max(
        1,
        query.index.bit_length()
        + query.max_steps.bit_length()
        + query.max_state_bits.bit_length(),
    )
    return ProjectedNumberTerm(
        FamilyId.ANTIHYDRA,
        query.index,
        None,
        2,
        SymbolicExpression(FamilyId.ANTIHYDRA, query.index),
        AntihydraTermPayload(term),
        ProjectionMetrics(
            FamilyId.ANTIHYDRA, query.index, 0, 0, 1, descriptor_bits, 4 + query.index
        ),
    )
