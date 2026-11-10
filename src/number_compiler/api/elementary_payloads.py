"""Payloads for closed-form elementary number families."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.symbolic_extent import Extent

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.numbers import (
        FermatNumberSpec,
        MersenneNumberSpec,
    )


@dataclass(frozen=True, slots=True)
class FermatTermPayload:
    spec: FermatNumberSpec

    @property
    def estimated_bit_length(self) -> Extent:
        return self.spec.bit_length_extent

    @source_reads_only
    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if index < 0 or not self.spec.bit_length_extent.contains_index(index):
            raise IndexError(index)
        return int(index == 0 or self.spec.exponent_extent == index)

    def materialize(self, *, max_bits: int) -> int:
        return self.spec.materialize(max_bits=max_bits)


@dataclass(frozen=True, slots=True)
class MersenneTermPayload:
    spec: MersenneNumberSpec

    @property
    def estimated_bit_length(self) -> int:
        return self.spec.bit_length

    @source_reads_only
    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if not 0 <= index < self.spec.bit_length:
            raise IndexError(index)
        return 1

    def materialize(self, *, max_bits: int) -> int:
        return self.spec.materialize(max_bits=max_bits)


@dataclass(frozen=True, slots=True)
class ScalarTermPayload:
    value: int

    def __post_init__(self) -> None:
        require_integer(self.value, "scalar term", 0)

    @property
    def estimated_bit_length(self) -> int:
        return max(1, int(self.value).bit_length())

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        if self.estimated_bit_length > max_bits:
            raise ValueError((self.estimated_bit_length, max_bits))
        return int(self.value)


__all__ = ["FermatTermPayload", "MersenneTermPayload", "ScalarTermPayload"]
