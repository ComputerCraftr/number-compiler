"""Stable public API facade for projected number terms."""

from typing import TYPE_CHECKING, Any

from number_compiler.api.lazy_exports import resolve_export as _resolve_export

if TYPE_CHECKING:
    from number_compiler.api.number_api import (
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

__all__ = [
    "FermatTermPayload",
    "FormulaTermPayload",
    "MersenneTermPayload",
    "NumberCompiler",
    "NumberFamily",
    "PoweredReverseAddTermPayload",
    "ProjectedNumberTerm",
    "ProjectionMetrics",
    "ScalarTermPayload",
]

_EXPORT_MODULES = {'FermatTermPayload': 'number_compiler.api.number_api',
 'FormulaTermPayload': 'number_compiler.api.number_api',
 'MersenneTermPayload': 'number_compiler.api.number_api',
 'NumberCompiler': 'number_compiler.api.number_api',
 'NumberFamily': 'number_compiler.api.number_api',
 'PoweredReverseAddTermPayload': 'number_compiler.api.number_api',
 'ProjectedNumberTerm': 'number_compiler.api.number_api',
 'ProjectionMetrics': 'number_compiler.api.number_api',
 'ScalarTermPayload': 'number_compiler.api.number_api'}


def __getattr__(name: str) -> Any:
    return _resolve_export(name, _EXPORT_MODULES, globals())


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(__all__))
