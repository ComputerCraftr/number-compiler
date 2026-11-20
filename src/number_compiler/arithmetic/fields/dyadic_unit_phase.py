"""Exact phase arithmetic and bounded carry/borrow frontiers over dyadic cuts.

The phase is only a compact representation of an odd multiplier power modulo
``2**precision``.  It does not authenticate a source, a recurrence, or a
periodic word; family issuers must establish those facts separately.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.input_validation import require_integer

UnitBase = Literal[3, 5, 15]
MAX_DYADIC_PHASE_PRECISION = 16_384


def _unit_order(base: UnitBase, precision: int) -> int:
    """Return the exact multiplicative order for the supported odd units."""
    if precision <= 1:
        return 1
    if base == 3:
        return 2 if precision == 2 else 1 << (precision - 2)
    if base == 5:
        return 1 if precision == 2 else 1 << (precision - 2)
    if precision <= 5:
        return 2
    return 1 << (precision - 4)


@dataclass(frozen=True, slots=True)
class DyadicUnitPhase:
    """An exponent phase for ``base**n mod 2**precision``.

    ``phase`` is canonical modulo the exact unit order at this precision.
    Moving to lower precision preserves the represented multiplier because
    these supported unit orders are compatible under dyadic reduction.
    """

    base: UnitBase
    precision: int
    phase: int

    def __post_init__(self) -> None:
        if type(self.base) is not int or self.base not in (3, 5, 15):
            raise ValueError("dyadic unit base must be 3, 5, or 15")
        if (
            type(self.precision) is not int
            or not 1 <= self.precision <= MAX_DYADIC_PHASE_PRECISION
        ):
            raise ValueError("dyadic phase precision is outside the supported bound")
        if type(self.phase) is not int or not 0 <= self.phase < _unit_order(
            self.base, self.precision
        ):
            raise ValueError("dyadic phase is not canonical for its unit order")

    @classmethod
    def from_exponent(
        cls, base: UnitBase, exponent: int, precision: int
    ) -> DyadicUnitPhase:
        """Reduce an exact nonnegative exponent to its dyadic unit phase."""
        exponent = require_integer(exponent, "dyadic exponent", 0)
        precision = require_integer(precision, "dyadic precision", 1)
        if precision > MAX_DYADIC_PHASE_PRECISION:
            raise ValueError("dyadic phase precision is outside the supported bound")
        if type(base) is not int or base not in (3, 5, 15):
            raise ValueError("dyadic unit base must be 3, 5, or 15")
        return cls(base, precision, exponent % _unit_order(base, precision))

    @property
    def order(self) -> int:
        return _unit_order(self.base, self.precision)

    @property
    def modulus(self) -> int:
        return 1 << self.precision

    @property
    def multiplier(self) -> int:
        return pow(self.base, self.phase, self.modulus)

    def multiplier_at(self, precision: int) -> int:
        """Return the same action reduced to at most the stored precision."""
        precision = require_integer(precision, "requested precision", 1)
        if precision > self.precision:
            raise ValueError("requested precision exceeds the authenticated phase")
        return pow(self.base, self.phase, 1 << precision)

    def advance(self, steps: int) -> DyadicUnitPhase:
        """Advance the represented temporal exponent by a nonnegative span."""
        steps = require_integer(steps, "phase advance", 0)
        return DyadicUnitPhase(
            self.base, self.precision, (self.phase + steps) % self.order
        )

    def square(self) -> DyadicUnitPhase:
        """Represent the square of this unit multiplier."""
        return DyadicUnitPhase(self.base, self.precision, (2 * self.phase) % self.order)

    def power(self, exponent: int) -> DyadicUnitPhase:
        """Represent a nonnegative power of this unit multiplier."""
        exponent = require_integer(exponent, "phase power", 0)
        return DyadicUnitPhase(
            self.base,
            self.precision,
            (self.phase * exponent) % self.order,
        )


@dataclass(frozen=True, slots=True)
class DyadicCarryCut:
    """Carry leaving a bounded low-column prefix at one bit cut."""

    position: int
    carry: int


@dataclass(frozen=True, slots=True)
class DyadicCarryFrontier:
    """Requested carries, returned in caller order with the action phase."""

    phase: DyadicUnitPhase
    cuts: tuple[DyadicCarryCut, ...]
    carry_width: int


def dyadic_carry_frontier(
    phase: DyadicUnitPhase,
    source: int,
    offset: int,
    positions: tuple[int, ...],
    *,
    carry_width: int,
    reserve_bits: Callable[[int], None],
) -> DyadicCarryFrontier:
    """Compute low-column affine carries only at the requested dyadic cuts.

    At cut ``j`` the value is
    ``floor((a**n * (source mod 2**j) + (offset mod 2**j)) / 2**j)``
    reduced to ``carry_width`` bits.  The upper input columns are deliberately
    excluded, matching digit-by-digit normalization rather than a quotient of
    the complete affine result.
    """
    source = require_integer(source, "carry source")
    offset = require_integer(offset, "carry offset")
    carry_width = require_integer(carry_width, "carry width", 1)
    if type(phase) is not DyadicUnitPhase:
        raise TypeError("carry frontier requires a typed dyadic phase")
    if type(positions) is not tuple or any(
        type(position) is not int or position < 0 for position in positions
    ):
        raise ValueError("carry positions must be a tuple of nonnegative integers")
    if not callable(reserve_bits):
        raise TypeError("carry frontier requires a scratch reservation callback")
    if not positions:
        return DyadicCarryFrontier(phase, (), carry_width)
    max_position = max(positions)
    required_precision = max_position + carry_width
    if required_precision > phase.precision:
        raise ValueError("carry frontier exceeds the authenticated dyadic phase")

    # Reserve the modular operands before constructing the largest mask or
    # product.  Repeated positions remain repeated in the result by design.
    reserve_bits(
        8
        * (
            required_precision
            + source.bit_length()
            + offset.bit_length()
            + len(positions) * (carry_width + 64)
            + 64
        )
    )
    multiplier = phase.multiplier_at(required_precision)
    mask = (1 << carry_width) - 1
    low_source = source & ((1 << max_position) - 1)
    low_offset = offset & ((1 << max_position) - 1)
    carries_by_position: dict[int, int] = {}
    for position in sorted(set(positions)):
        numerator_precision = position + carry_width
        local_mask = (1 << numerator_precision) - 1
        input_mask = (1 << position) - 1
        local_multiplier = multiplier & local_mask
        numerator = (
            local_multiplier * (low_source & input_mask) + (low_offset & input_mask)
        ) & local_mask
        carries_by_position[position] = (numerator >> position) & mask
    cuts = tuple(
        DyadicCarryCut(position, carries_by_position[position])
        for position in positions
    )
    return DyadicCarryFrontier(phase, cuts, carry_width)


@dataclass(frozen=True, slots=True)
class DyadicBorrowCut:
    """One exact chunk of a source-bound subtraction at a dyadic cut."""

    position: int
    width: int
    raw_chunk: int
    correction_chunk: int
    physical_chunk: int
    borrow_in: int
    borrow_out: int


@dataclass(frozen=True, slots=True)
class DyadicBorrowFrontier:
    """Chronologically indexed chunk observations for a subtraction."""

    raw_phase: DyadicUnitPhase
    correction_phase: DyadicUnitPhase
    cuts: tuple[DyadicBorrowCut, ...]


def dyadic_borrow_frontier(
    raw_phase: DyadicUnitPhase,
    raw_source: int,
    correction_phase: DyadicUnitPhase,
    correction_source: int,
    positions: tuple[int, ...],
    *,
    chunk_width: int,
    reserve_bits: Callable[[int], None],
) -> DyadicBorrowFrontier:
    """Project ``a**n*u - b**m*v`` into bounded ordered dyadic chunks.

    Borrow at a cut is determined by the exact low residues, and each returned
    chunk is the corresponding two's-complement difference modulo its chunk
    width.  This is arithmetic for the two supplied powers; it does not assert
    that either source word is periodic or authorize later recurrence steps.
    """
    raw_source = require_integer(raw_source, "raw borrow source")
    correction_source = require_integer(correction_source, "correction source")
    chunk_width = require_integer(chunk_width, "borrow chunk width", 1)
    if (
        type(raw_phase) is not DyadicUnitPhase
        or type(correction_phase) is not DyadicUnitPhase
    ):
        raise TypeError("borrow frontier requires typed dyadic phases")
    if type(positions) is not tuple or any(
        type(position) is not int or position < 0 for position in positions
    ):
        raise ValueError("borrow positions must be a tuple of nonnegative integers")
    if not callable(reserve_bits):
        raise TypeError("borrow frontier requires a scratch reservation callback")
    if not positions:
        return DyadicBorrowFrontier(raw_phase, correction_phase, ())
    max_precision = max(positions) + chunk_width
    if max_precision > min(raw_phase.precision, correction_phase.precision):
        raise ValueError("borrow frontier exceeds an authenticated dyadic phase")
    reserve_bits(
        8
        * (
            max_precision
            + raw_source.bit_length()
            + correction_source.bit_length()
            + len(positions) * (2 * chunk_width + 96)
            + 96
        )
    )
    raw_multiplier = raw_phase.multiplier_at(max_precision)
    correction_multiplier = correction_phase.multiplier_at(max_precision)
    prefix_mask = (1 << max_precision) - 1
    raw_prefix_window = (raw_multiplier * (raw_source & prefix_mask)) & prefix_mask
    correction_prefix_window = (
        correction_multiplier * (correction_source & prefix_mask)
    ) & prefix_mask
    width_mask = (1 << chunk_width) - 1
    chunk_modulus = 1 << chunk_width
    chunks_by_position: dict[int, DyadicBorrowCut] = {}
    for position in sorted(set(positions)):
        low_mask = (1 << position) - 1
        raw_low = raw_prefix_window & low_mask
        correction_low = correction_prefix_window & low_mask
        borrow_in = int(raw_low < correction_low)
        upper_mask = (1 << (position + chunk_width)) - 1
        raw_prefix = raw_prefix_window & upper_mask
        correction_prefix = correction_prefix_window & upper_mask
        raw_chunk = (raw_prefix >> position) & width_mask
        correction_chunk = (correction_prefix >> position) & width_mask
        physical_chunk = (raw_chunk - correction_chunk - borrow_in) & width_mask
        borrow_out = int((raw_prefix & upper_mask) < (correction_prefix & upper_mask))
        if physical_chunk != (raw_chunk - correction_chunk - borrow_in) % chunk_modulus:
            raise ArithmeticError("dyadic borrow chunk lost modular subtraction")
        chunks_by_position[position] = DyadicBorrowCut(
            position,
            chunk_width,
            raw_chunk,
            correction_chunk,
            physical_chunk,
            borrow_in,
            borrow_out,
        )
    chunks = tuple(chunks_by_position[position] for position in positions)
    return DyadicBorrowFrontier(raw_phase, correction_phase, chunks)


__all__ = [
    "DyadicBorrowCut",
    "DyadicBorrowFrontier",
    "DyadicCarryCut",
    "DyadicCarryFrontier",
    "DyadicUnitPhase",
    "MAX_DYADIC_PHASE_PRECISION",
    "dyadic_borrow_frontier",
    "dyadic_carry_frontier",
]
