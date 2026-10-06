"""Private records shared by the iterative tile scheduler and its applications."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_context import ChildContext
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey


@dataclass(slots=True)
class _DirectFrame:
    key: PoweredResultKey
    stage: int = 0
    left_context: ChildContext | None = None
    right_context: ChildContext | None = None
    checked_miss: bool = False


_APPLICATION_SEAL = object()

__all__ = ["_APPLICATION_SEAL", "_DirectFrame"]
