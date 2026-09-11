"""Supported number compilation, sequence, term, and resource APIs."""

from number_compiler.api.number_api import (
    FermatTermPayload,
    FormulaTermPayload,
    MersenneTermPayload,
    NumberCompiler,
    NumberFamily,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
    ProjectedNumberTerm,
    ProjectionMetrics,
    ScalarTermPayload,
    TermPayload,
)
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzCompilation,
    CollatzRawFieldQuotient,
    CollatzSequenceSpec,
    FactoredRadixProjection,
    FermatCompilation,
    FermatCompiledTerm,
    FermatSequenceSpec,
    MersenneCompilation,
    MersenneCompiledTerm,
    MersenneSequenceSpec,
    PrimeBlockCompilation,
    PrimeBlockSequenceSpec,
    PrimeFactoredAutomatonCompilation,
    RadixTermMetrics,
    ReverseAddCompilation,
    ReverseAddSequenceSpec,
    SpecialCompilation,
    SpecialDepthCertificateSummary,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import (
    CollatzPhysicalBlockMetrics,
    PoweredCollatzTerm,
)
from number_compiler.sequences.reverse_add.power import (
    ReverseAddPoweredTerm,
    ReverseAddPowerMetrics,
)

__all__ = [
    "BlockContextBudget",
    "BlockContextBudgetExceeded",
    "CanonicalSequenceCompiler",
    "CollatzCompilation",
    "CollatzPhysicalBlockMetrics",
    "CollatzRawFieldQuotient",
    "CollatzSequenceSpec",
    "FactoredRadixProjection",
    "FermatCompilation",
    "FermatCompiledTerm",
    "FermatSequenceSpec",
    "FermatTermPayload",
    "FormulaTermPayload",
    "MersenneCompilation",
    "MersenneCompiledTerm",
    "MersenneSequenceSpec",
    "MersenneTermPayload",
    "NumberCompiler",
    "NumberFamily",
    "PoweredCollatzTerm",
    "PoweredCollatzTermPayload",
    "PoweredReverseAddTermPayload",
    "TermPayload",
    "PrimeBlockCompilation",
    "PrimeBlockSequenceSpec",
    "PrimeFactoredAutomatonCompilation",
    "ProjectedNumberTerm",
    "ProjectionMetrics",
    "RadixTermMetrics",
    "ResourceLedger",
    "ReverseAddCompilation",
    "ReverseAddPowerMetrics",
    "ReverseAddPoweredTerm",
    "ReverseAddSequenceSpec",
    "ScalarTermPayload",
    "SpecialCompilation",
    "SpecialDepthCertificateSummary",
]
