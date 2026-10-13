"""Projection adapters for exact Fermat and Mersenne number descriptors."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.elementary_payloads import (
    FermatTermPayload,
    MersenneTermPayload,
)
from number_compiler.api.number_api import ProjectedNumberTerm, ProjectionMetrics
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
        "fermat",
        query.index,
        query.index,
        2,
        SymbolicExpression("fermat", query.index),
        FermatTermPayload(spec),
        ProjectionMetrics(
            "fermat",
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
        "mersenne",
        query.index,
        query.index,
        2,
        SymbolicExpression("mersenne", query.index),
        MersenneTermPayload(spec),
        ProjectionMetrics(
            "mersenne",
            query.index,
            0,
            0,
            1,
            spec.description_bits,
            spec.bit_length,
        ),
    )
