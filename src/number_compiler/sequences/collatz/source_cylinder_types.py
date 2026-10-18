"""Exact source-cylinder cache records and their canonical coefficients."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        _CanonicalGain,
    )


def _canonical_gain(odd_symbols: int) -> int:
    """Return the exact gain for one admitted odd-symbol count."""
    if type(odd_symbols) is not int or odd_symbols < 0:
        raise ValueError("Collatz odd-symbol count must be a natural integer")
    return int(3**odd_symbols)


def _low_residue(value: int, width: int) -> int:
    """Return low-width bits without allocating a wider mask than needed."""
    if width >= value.bit_length():
        return value
    return value & ((1 << width) - 1)


def _admit_source_key(source: int, width: int) -> tuple[int, int]:
    """Validate one source germ and return its residue and actual key size."""
    if type(source) is not int or source <= 0:
        raise ValueError("Collatz macro source must be positive")
    if type(width) is not int or width < 8 or width & (width - 1):
        raise ValueError("Collatz macro width must be dyadic and at least eight")
    return _low_residue(source, width), source.bit_length() + width.bit_length()


@dataclass(frozen=True, slots=True)
class CollatzDyadicOccurrence:
    width: int
    residue: int
    odd_symbols: int
    target_origin: int
    multiplier: int

    def __post_init__(self) -> None:
        self._validate(None)
        self._validate(_canonical_gain(self.odd_symbols))

    def _validate(self, canonical_gain: int | None) -> None:
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

    @classmethod
    def _from_gain(
        cls,
        width: int,
        residue: int,
        odd_symbols: int,
        target_origin: int,
        gain: _CanonicalGain,
    ) -> CollatzDyadicOccurrence:
        from number_compiler.sequences.collatz.source_cylinder_cache import (
            _CanonicalGain as CanonicalGain,
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
        occurrence._validate(gain.multiplier)
        return occurrence

    def apply(self, source: int) -> int:
        if type(source) is not int or source < 0:
            raise ValueError("Collatz cylinder needs a nonnegative exact source")
        if _low_residue(source, self.width) != self.residue:
            raise ValueError("Collatz cylinder source germ differs")
        return self.target_origin + self.multiplier * (source >> self.width)


__all__ = ["CollatzDyadicOccurrence"]
