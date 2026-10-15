"""Projection adapters for exact Fermat and Mersenne number descriptors."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.elementary_payloads import (
    FermatTermPayload,
    MersenneTermPayload,
)
from number_compiler.api.number_api import ProjectedNumberTerm, ProjectionMetrics
from number_compiler.api.observation_types import FamilyId
from number_compiler.api.symbolic_terms import SymbolicExpression
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import FermatTermQuery, MersenneTermQuery


def project_fermat(
    _compiler: NumberCompiler, query: FermatTermQuery
) -> ProjectedNumberTerm:
    spec = FermatNumberSpec(query.index)
    return ProjectedNumberTerm(
        FamilyId.FERMAT,
        query.index,
        query.index,
        2,
        SymbolicExpression(FamilyId.FERMAT, query.index),
        FermatTermPayload(spec),
        ProjectionMetrics(
            FamilyId.FERMAT,
            query.index,
            0,
            0,
            1,
            spec.description_bits,
            spec.bit_length_extent,
        ),
    )


def project_mersenne(
    _compiler: NumberCompiler, query: MersenneTermQuery
) -> ProjectedNumberTerm:
    spec = MersenneNumberSpec(query.index)
    return ProjectedNumberTerm(
        FamilyId.MERSENNE,
        query.index,
        query.index,
        2,
        SymbolicExpression(FamilyId.MERSENNE, query.index),
        MersenneTermPayload(spec),
        ProjectionMetrics(
            FamilyId.MERSENNE,
            query.index,
            0,
            0,
            1,
            spec.description_bits,
            spec.bit_length,
        ),
    )
