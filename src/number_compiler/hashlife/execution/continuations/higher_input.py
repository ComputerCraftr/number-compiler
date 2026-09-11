"""Immutable source boundaries for legacy K/U proof bindings."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.hashlife.execution.field_images import SourceCellID


RuntimeInputCellID: TypeAlias = SourceCellID


@dataclass(frozen=True, slots=True)
class InputCellGeometry:
    level: int
    uniform_symbol: int | None


__all__ = [
    "InputCellGeometry",
    "RuntimeInputCellID",
]
