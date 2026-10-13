"""Payload adapters for decimal reverse recurrences."""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.symbolic_extent import Extent
from number_compiler.sequences.reverse_add.extent import ReverseAddBitExtent

if TYPE_CHECKING:
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
    from number_compiler.sequences.reverse_add.power import (
        ReverseAddPoweredTerm,
        ReverseAddPowerMetrics,
    )


@dataclass(frozen=True, slots=True)
class PoweredReverseAddTermPayload:
    term: ReverseAddPoweredTerm

    def __post_init__(self) -> None:
        from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

        if type(self.term) is not ReverseAddPoweredTerm:
            raise TypeError("powered reverse payload requires its exact term type")

    @property
    def estimated_bit_length(self) -> Extent:
        # Keep the exact bit cap lazy for the same reason as the exact radix
        # width: construction itself must not execute the endpoint transducer.
        return ReverseAddBitExtent(self.term.seed, self.term.base, self.term.generation)

    def digits(self) -> tuple[int, ...]:
        return self.term.digits()

    def iter_digits(self, *, reverse: bool = False) -> Iterator[int]:
        if type(reverse) is not bool:
            raise TypeError("reverse must be a Boolean")
        if not reverse:
            return self.term.iter_digits()
        # Text emission is already linear in the digit count.  Reversing the
        # final stream here does not pollute pre-print construction/projection.
        return iter(reversed(self.term.digits()))

    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if index < 0:
            raise IndexError(index)
        self.term._prepare_recursive_source_authority()
        return self._digit_source_only(index)

    @source_reads_only
    def _digit_source_only(self, index: int) -> int:
        return self.term.digit(index)

    def materialize(self, *, max_bits: int) -> int:
        return self.term.materialize(max_bits=max_bits)

    def power_metrics(self) -> ReverseAddPowerMetrics:
        return self.term.metrics()


@dataclass(frozen=True, slots=True)
class DoubleReverseTermPayload:
    """Demand adapter for the fixed decimal U(n)=2*reverse(n) recurrence."""

    term: DoubleReverseTerm

    def __post_init__(self) -> None:
        from number_compiler.sequences.double_reverse.power import DoubleReverseTerm

        if type(self.term) is not DoubleReverseTerm:
            raise TypeError("double-reverse payload requires its exact term type")

    @property
    def estimated_bit_length(self) -> int:
        return 4 * self.term.maximum_width

    def digits(self) -> tuple[int, ...]:
        return tuple(self.term.iter_digits())

    def iter_digits(self) -> Iterator[int]:
        return self.term.iter_digits()

    def digit(self, index: int) -> int:
        return self.term.digit(index)

    def materialize(self, *, max_bits: int) -> int:
        return self.term.materialize(max_bits=max_bits)
