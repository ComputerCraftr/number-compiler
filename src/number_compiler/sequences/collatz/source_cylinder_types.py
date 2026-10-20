"""Exact source-cylinder cache records and their canonical coefficients."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CanonicalGain,
    )


def canonical_gain(odd_symbols: int) -> int:
    """Return the exact gain for one admitted odd-symbol count."""
    if type(odd_symbols) is not int or odd_symbols < 0:
        raise ValueError("Collatz odd-symbol count must be a natural integer")
    return int(3**odd_symbols)


def _low_residue(value: int, width: int) -> int:
    """Return low-width bits without allocating a wider mask than needed."""
    if width >= value.bit_length():
        return value
    return value & ((1 << width) - 1)


def admit_source_key(source: int, width: int) -> tuple[int, int]:
    """Validate one source germ and return its residue and actual key size."""
    if type(source) is not int or source <= 0:
        raise ValueError("Collatz macro source must be positive")
    if type(width) is not int or width < 8 or width & (width - 1):
        raise ValueError("Collatz macro width must be dyadic and at least eight")
    return _low_residue(source, width), source.bit_length() + width.bit_length()


def validate_width_summary(
    summary: CollatzTapeWidthSummary, source: int, width: int
) -> None:
    """Validate a width summary against its exact Collatz source cylinder."""
    if type(summary) is not CollatzTapeWidthSummary:
        raise ValueError("Collatz exact width spine is malformed or detached")
    if type(summary.blank) is not BlankLedger:
        raise ValueError("Collatz exact width spine has a foreign blank ledger")
    # Frozen dataclasses can still be tampered with through object.__setattr__.
    # Re-run canonical validation before trusting any cached field.
    summary.blank.__post_init__()
    summary.__post_init__()
    if (
        summary.source_width != source.bit_length()
        or summary.normalized_symbols != width
        or summary.physical_ticks != width + summary.odd_steps
        or summary.odd_steps > width
        or summary.target_width <= 0
        or summary.blank.delta != summary.target_width - summary.source_width
    ):
        raise ValueError("Collatz exact width spine is malformed or detached")


def decode_width_summary(
    payload: object, source: int, width: int
) -> tuple[CollatzTapeWidthSummary, int]:
    """Decode, validate, and measure one shared width-spine payload."""
    if not is_exact_object_tuple(payload):
        raise ValueError("Collatz shared width spine payload is invalid")
    values = payload
    if len(values) != 8 or any(type(value) is not int for value in values):
        raise ValueError("Collatz shared width spine payload is invalid")
    integer_values = cast(tuple[int, int, int, int, int, int, int, int], values)
    (
        source_width,
        target_width,
        physical,
        normalized,
        odd,
        delta,
        minimum,
        maximum,
    ) = integer_values
    summary = CollatzTapeWidthSummary(
        source_width,
        target_width,
        physical,
        normalized,
        odd,
        BlankLedger(delta, minimum, maximum),
    )
    validate_width_summary(summary, source, width)
    return summary, sum(value.bit_length() for value in integer_values)


@dataclass(frozen=True, slots=True)
class CollatzDyadicOccurrence:
    width: int
    residue: int
    odd_symbols: int
    target_origin: int
    multiplier: int

    def __post_init__(self) -> None:
        self.validate(None)
        self.validate(canonical_gain(self.odd_symbols))

    def validate(self, canonical_gain: int | None) -> None:
        if any(
            type(value) is not int
            for value in (
                self.width,
                self.residue,
                self.odd_symbols,
                self.target_origin,
                self.multiplier,
            )
        ):
            raise TypeError("Collatz occurrence coordinates require exact integers")
        if self.width < 8 or self.width & (self.width - 1):
            raise ValueError("Collatz occurrence width must be dyadic")
        if (
            self.residue < 0
            or self.residue.bit_length() > self.width
            or not 0 <= self.odd_symbols <= self.width
        ):
            raise ValueError("Collatz occurrence germ or odd count is invalid")
        if self.multiplier <= 0 or not 0 <= self.target_origin < self.multiplier:
            raise ValueError("Collatz occurrence centered coefficients are invalid")
        if canonical_gain is not None and self.multiplier != canonical_gain:
            raise ValueError("Collatz occurrence centered coefficients are invalid")

    def validate_canonical_gain(self, canonical_gain: int | None = None) -> None:
        """Recheck the admitted occurrence fields against an optional gain."""
        self.validate(canonical_gain)

    @classmethod
    def from_canonical_gain(
        cls,
        width: int,
        residue: int,
        odd_symbols: int,
        target_origin: int,
        gain: CanonicalGain,
    ) -> CollatzDyadicOccurrence:
        from number_compiler.sequences.collatz.source_cylinder_cache import (
            CanonicalGain as CanonicalGain,
        )

        if (
            type(gain) is not CanonicalGain
            or type(odd_symbols) is not int
            or gain.odd_symbols != odd_symbols
            or type(gain.multiplier) is not int
            or gain.multiplier <= 0
        ):
            raise ValueError("Collatz occurrence has invalid canonical gain")
        occurrence = object.__new__(cls)
        object.__setattr__(occurrence, "width", width)
        object.__setattr__(occurrence, "residue", residue)
        object.__setattr__(occurrence, "odd_symbols", odd_symbols)
        object.__setattr__(occurrence, "target_origin", target_origin)
        object.__setattr__(occurrence, "multiplier", gain.multiplier)
        occurrence.validate(gain.multiplier)
        return occurrence

    def apply(self, source: int) -> int:
        if type(source) is not int or source < 0:
            raise ValueError("Collatz cylinder needs a nonnegative exact source")
        if _low_residue(source, self.width) != self.residue:
            raise ValueError("Collatz cylinder source germ differs")
        return self.target_origin + self.multiplier * (source >> self.width)


__all__ = [
    "CollatzDyadicOccurrence",
    "admit_source_key",
    "canonical_gain",
    "decode_width_summary",
    "validate_width_summary",
]
