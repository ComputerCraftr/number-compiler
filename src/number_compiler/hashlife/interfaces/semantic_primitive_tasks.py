"""Shared scheduler requests for complete primitive-cell effects."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientID


@dataclass(frozen=True, slots=True)
class PrimitiveMacroKey:
    kernel: ActionProgramID
    source: CellID


@dataclass(frozen=True, slots=True)
class PrimitiveMacroObservation:
    """One transient observation of a complete function, never a cache key."""

    quotient: DiamondQuotientID
    channel: str
    left: int
    right: int
    coordinate: int


PrimitiveMacroTask: TypeAlias = PrimitiveMacroKey | PrimitiveMacroObservation
