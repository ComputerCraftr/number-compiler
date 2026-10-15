"""Stable public API facade for projected number terms."""

from typing import TYPE_CHECKING, Any

from number_compiler.api.lazy_exports import resolve_export as _resolve_export

if TYPE_CHECKING:
    from number_compiler.api.number_api import (
        DoubleReverseTermPayload,
        FermatTermPayload,
        FormulaTermPayload,
        MersenneTermPayload,
        NumberCompiler,
        NumberFamily,
        PoweredReverseAddTermPayload,
        ProjectedNumberTerm,
        ProjectionMetrics,
        ScalarTermPayload,
    )
    from number_compiler.api.observation_types import (
        FamilyId,
        IndexEncoding,
        IndexUnit,
        ObservationCategory,
        ObservationId,
        ObservationSpec,
        OutputFormat,
        OutputStatus,
        SelectorId,
    )
    from number_compiler.api.query_types import (
        AntihydraTermQuery,
        AntihydraVerifyQuery,
        CollatzEventQuery,
        CollatzTermQuery,
        CommaTermQuery,
        DoubleReverseTermQuery,
        ExecutionQuery,
        FermatTermQuery,
        MersenneTermQuery,
        PrimeTermQuery,
        ReverseAddTermQuery,
        TermQuery,
    )

__all__ = [
    "AntihydraTermQuery",
    "AntihydraVerifyQuery",
    "CollatzEventQuery",
    "CollatzTermQuery",
    "CommaTermQuery",
    "DoubleReverseTermPayload",
    "DoubleReverseTermQuery",
    "ExecutionQuery",
    "FamilyId",
    "FermatTermPayload",
    "FermatTermQuery",
    "FormulaTermPayload",
    "IndexEncoding",
    "IndexUnit",
    "MersenneTermPayload",
    "MersenneTermQuery",
    "NumberCompiler",
    "NumberFamily",
    "ObservationCategory",
    "ObservationId",
    "ObservationSpec",
    "OutputFormat",
    "OutputStatus",
    "PoweredReverseAddTermPayload",
    "PrimeTermQuery",
    "ProjectedNumberTerm",
    "ProjectionMetrics",
    "ReverseAddTermQuery",
    "ScalarTermPayload",
    "SelectorId",
    "TermQuery",
]

_EXPORT_MODULES = {
    "AntihydraTermQuery": "number_compiler.api.query_types",
    "AntihydraVerifyQuery": "number_compiler.api.query_types",
    "CollatzEventQuery": "number_compiler.api.query_types",
    "CollatzTermQuery": "number_compiler.api.query_types",
    "CommaTermQuery": "number_compiler.api.query_types",
    "DoubleReverseTermQuery": "number_compiler.api.query_types",
    "DoubleReverseTermPayload": "number_compiler.api.number_api",
    "ExecutionQuery": "number_compiler.api.query_types",
    "FamilyId": "number_compiler.api.observation_types",
    "FermatTermPayload": "number_compiler.api.number_api",
    "FermatTermQuery": "number_compiler.api.query_types",
    "IndexEncoding": "number_compiler.api.observation_types",
    "IndexUnit": "number_compiler.api.observation_types",
    "FormulaTermPayload": "number_compiler.api.number_api",
    "MersenneTermPayload": "number_compiler.api.number_api",
    "MersenneTermQuery": "number_compiler.api.query_types",
    "NumberCompiler": "number_compiler.api.number_api",
    "NumberFamily": "number_compiler.api.number_api",
    "PrimeTermQuery": "number_compiler.api.query_types",
    "PoweredReverseAddTermPayload": "number_compiler.api.number_api",
    "ProjectedNumberTerm": "number_compiler.api.number_api",
    "ProjectionMetrics": "number_compiler.api.number_api",
    "ObservationCategory": "number_compiler.api.observation_types",
    "ObservationId": "number_compiler.api.observation_types",
    "ObservationSpec": "number_compiler.api.observation_types",
    "OutputFormat": "number_compiler.api.observation_types",
    "OutputStatus": "number_compiler.api.observation_types",
    "ReverseAddTermQuery": "number_compiler.api.query_types",
    "ScalarTermPayload": "number_compiler.api.number_api",
    "SelectorId": "number_compiler.api.observation_types",
    "TermQuery": "number_compiler.api.query_types",
}


def __getattr__(name: str) -> Any:
    return _resolve_export(name, _EXPORT_MODULES, globals())


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(__all__))
