"""Supported number compilation, sequence, term, and resource APIs."""

from typing import TYPE_CHECKING, Any

from number_compiler.api.lazy_exports import resolve_export as _resolve_export

if TYPE_CHECKING:
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
    "TermPayload",
]

_EXPORT_MODULES = {
    "FermatTermPayload": "number_compiler.api.number_api",
    "FormulaTermPayload": "number_compiler.api.number_api",
    "MersenneTermPayload": "number_compiler.api.number_api",
    "NumberCompiler": "number_compiler.api.number_api",
    "NumberFamily": "number_compiler.api.number_api",
    "PoweredCollatzTermPayload": "number_compiler.api.number_api",
    "PoweredReverseAddTermPayload": "number_compiler.api.number_api",
    "ProjectedNumberTerm": "number_compiler.api.number_api",
    "ProjectionMetrics": "number_compiler.api.number_api",
    "ScalarTermPayload": "number_compiler.api.number_api",
    "TermPayload": "number_compiler.api.number_api",
    "CanonicalSequenceCompiler": "number_compiler.api.sequence_compiler",
    "CollatzCompilation": "number_compiler.api.sequence_types",
    "CollatzRawFieldQuotient": "number_compiler.api.sequence_types",
    "CollatzSequenceSpec": "number_compiler.api.sequence_types",
    "FactoredRadixProjection": "number_compiler.api.sequence_types",
    "FermatCompilation": "number_compiler.api.sequence_types",
    "FermatCompiledTerm": "number_compiler.api.sequence_types",
    "FermatSequenceSpec": "number_compiler.api.sequence_types",
    "MersenneCompilation": "number_compiler.api.sequence_types",
    "MersenneCompiledTerm": "number_compiler.api.sequence_types",
    "MersenneSequenceSpec": "number_compiler.api.sequence_types",
    "PrimeBlockCompilation": "number_compiler.api.sequence_types",
    "PrimeBlockSequenceSpec": "number_compiler.api.sequence_types",
    "PrimeFactoredAutomatonCompilation": "number_compiler.api.sequence_types",
    "RadixTermMetrics": "number_compiler.api.sequence_types",
    "ReverseAddCompilation": "number_compiler.api.sequence_types",
    "ReverseAddSequenceSpec": "number_compiler.api.sequence_types",
    "SpecialCompilation": "number_compiler.api.sequence_types",
    "SpecialDepthCertificateSummary": "number_compiler.api.sequence_types",
    "BlockContextBudget": "number_compiler.arithmetic.contracts.block_effect",
    "BlockContextBudgetExceeded": "number_compiler.arithmetic.contracts.block_effect",
    "ResourceLedger": "number_compiler.resources.ledger",
    "CollatzPhysicalBlockMetrics": "number_compiler.sequences.collatz.block_power",
    "PoweredCollatzTerm": "number_compiler.sequences.collatz.block_power",
    "ReverseAddPoweredTerm": "number_compiler.sequences.reverse_add.power",
    "ReverseAddPowerMetrics": "number_compiler.sequences.reverse_add.power",
}


def __getattr__(name: str) -> Any:
    return _resolve_export(name, _EXPORT_MODULES, globals())


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(__all__))
