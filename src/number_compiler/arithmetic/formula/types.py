from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from number_compiler.arithmetic.fields.radix import bit_width

_bits = bit_width


def _mask(width: int) -> int:
    return (1 << int(width)) - 1 if width > 0 else 0


@dataclass(frozen=True, slots=True)
class RadixSpec:
    base: int = 10

    def __post_init__(self) -> None:
        if self.base < 2:
            raise ValueError("base must be >= 2")

    @property
    def threshold(self) -> int:
        return self.base - 1

    @property
    def pair_max(self) -> int:
        return 2 * (self.base - 1)

    @property
    def plane_count(self) -> int:
        return max(1, self.pair_max.bit_length())


@dataclass(frozen=True, slots=True)
class Expr:
    id: int
    kind: str
    width: int
    args: tuple[Expr, ...]
    param: tuple[int | str, ...]
    local_param_bits: int


class FormulaStorage:
    """Shared storage contract for construction and evaluation mixins."""

    __slots__ = (
        "_closed_bit_count",
        "_closed_known",
        "_closed_values",
        "_derived",
        "_metadata",
        "_next_id",
        "_nodes",
    )
    _next_id: int
    _nodes: dict[tuple[object, ...], Expr]
    _closed_known: dict[int, int]
    _closed_values: dict[int, int]
    _closed_bit_count: int
    _derived: dict[tuple[object, ...], Expr]
    _metadata: dict[tuple[object, ...], Any]


__all__ = ["Expr", "RadixSpec"]
