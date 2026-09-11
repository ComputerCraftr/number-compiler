"""Lazy character observers for accelerated Collatz sources.

These projections deliberately sit *before* the exact valuation/root-germ path.
For a positive odd source ``n`` the accelerated step is

    H(n) = (3*n + 1) / 2**k,   k = v2(3*n+1).

The strict-growth bit does not require ``k``: it is exactly the primitive
Dirichlet character modulo four, ``chi_4(n)=(-1/n)``.  A cyclic/cyclotomic
observer that only needs the radial shift modulo ``m`` likewise should not
retain the full valuation; on a power-of-four source word it can accumulate
``k mod m`` directly from the first non-sentinel run.

Neither object is a closed Collatz orbit state.  They are exact lazy observers.
The full 2-adic germ remains the fallback when an exact valuation/successor is
actually requested.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from math import gcd, lcm

from number_compiler.arithmetic.automata.program_word import (
    CanonicalWord,
    first_run,
    iter_runs,
)
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.raw_field import (
    collatz_sentinel_digit,
    power4_radix_bits,
)


@dataclass(frozen=True, slots=True)
class CollatzGrowthCharacter:
    """Primitive modulo-four character deciding the next growth direction.

    For odd ``n``::

        chi4(n) = +1  <=> n == 1 (mod 4) <=> v2(3*n+1) >= 2
        chi4(n) = -1  <=> n == 3 (mod 4) <=> v2(3*n+1) == 1

    Therefore the character decides strict increase without acquiring the
    complete 2-adic valuation.
    """

    symbol: int

    def __post_init__(self) -> None:
        if type(self.symbol) is not int:
            raise TypeError("Collatz growth characters require an exact integer")
        symbol = self.symbol
        if symbol not in (-1, 1):
            raise ValueError(symbol)
        object.__setattr__(self, "symbol", symbol)

    @classmethod
    def from_odd_value(cls, value: int) -> CollatzGrowthCharacter:
        if type(value) is not int:
            raise TypeError("Collatz character input must be an exact integer")
        if value <= 0 or not (value & 1):
            raise ValueError(value)
        return cls(1 if value & 3 == 1 else -1)

    @classmethod
    def from_power4_word(
        cls,
        word: CanonicalWord,
        *,
        base: int = 4,
    ) -> CollatzGrowthCharacter:
        power4_radix_bits(base)
        if not isinstance(word, CanonicalWord) or not word.length:
            raise ValueError("positive odd source word required")
        low = first_run(word)
        if low.symbol is None:
            raise AssertionError(low)
        digit = int(low.symbol)
        if not 0 <= digit < int(base) or not (digit & 1):
            raise ValueError((base, digit))
        residue = digit & 3
        if residue not in (1, 3):
            raise AssertionError((base, digit, residue))
        return cls(1 if residue == 1 else -1)

    @property
    def increases(self) -> bool:
        return self.symbol == -1

    @property
    def nonincreasing(self) -> bool:
        return self.symbol == 1

    @property
    def phase_symbol(self) -> int:
        """Compatibility bit: one for strict growth, zero otherwise."""
        return int(self.increases)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-growth-chi4", self.symbol)

    @property
    def description_bits(self) -> int:
        return 1


@dataclass(frozen=True, slots=True)
class CollatzRadialCharacter:
    """Exact cyclic character coordinate for a radial binary shift.

    ``shift`` is ``k mod order`` for ``k=v2(3*n+1)``.  An order-``order``
    Fourier/cyclotomic lane ``j`` sees multiplication by
    ``omega**(-j*k)``, represented exactly by :meth:`lane_exponent` without
    introducing complex numbers or retaining the full valuation.
    """

    order: int
    shift: int

    def __post_init__(self) -> None:
        if type(self.order) is not int or type(self.shift) is not int:
            raise TypeError("Collatz radial characters require exact integers")
        order = self.order
        if order <= 0:
            raise ValueError(order)
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "shift", self.shift % order)

    def lane_exponent(self, lane: int = 1) -> int:
        if type(lane) is not int:
            raise TypeError("Collatz character lanes require exact integers")
        return (-lane * self.shift) % self.order

    def then(self, other: CollatzRadialCharacter) -> CollatzRadialCharacter:
        if self.order != other.order:
            raise ValueError((self.order, other.order))
        return CollatzRadialCharacter(self.order, self.shift + other.shift)

    def quotient(self, order: int) -> CollatzRadialCharacter:
        """Project a master character onto a divisor order without re-reading the source."""
        if type(order) is not int:
            raise TypeError("Collatz character orders require exact integers")
        if order <= 0 or self.order % order:
            raise ValueError((self.order, order))
        return CollatzRadialCharacter(order, self.shift)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-radial-character", self.order, self.shift)

    @property
    def description_bits(self) -> int:
        return bit_width(self.order) + bit_width(self.shift)


def collatz_growth_character_value(value: int) -> CollatzGrowthCharacter:
    return CollatzGrowthCharacter.from_odd_value(value)


def collatz_growth_character_word(
    word: CanonicalWord,
    *,
    base: int = 4,
) -> CollatzGrowthCharacter:
    return CollatzGrowthCharacter.from_power4_word(word, base=base)


def collatz_radial_character_value(value: int, order: int) -> CollatzRadialCharacter:
    """Project ``v2(3*n+1) mod order`` from a concrete odd integer.

    Python's integer low-bit operation used by :func:`v2_positive` obtains the
    exact valuation efficiently for a concrete integer.  This entry point still
    avoids every Collatz successor/root-germ construction; compressed words can
    use :func:`collatz_radial_character_word` to avoid retaining the full
    valuation coordinate entirely.
    """
    if type(value) is not int or type(order) is not int:
        raise TypeError("Collatz radial projection requires exact integers")
    if value <= 0 or not (value & 1) or order <= 0:
        raise ValueError((value, order))
    return CollatzRadialCharacter(order, v2_positive(3 * value + 1) % order)


def collatz_radial_character_word(
    word: CanonicalWord,
    order: int,
    *,
    base: int = 4,
) -> CollatzRadialCharacter:
    """Project only ``k mod order`` from a compressed power-of-four word.

    Complete sentinel runs contribute ``count*log2(base) mod order``.  At the
    first non-sentinel digit only its bounded local valuation is needed.  The
    routine visits canonical *runs*, never their represented digit counts, and
    never constructs ``k``, a successor word, a parity itinerary, or a 2-adic
    root-germ transition.
    """
    if type(order) is not int:
        raise TypeError("Collatz radial projection requires an exact order")
    bits = power4_radix_bits(base)
    if order <= 0 or not isinstance(word, CanonicalWord) or not word.length:
        raise ValueError((order, word))
    sentinel = collatz_sentinel_digit(base)
    shift = 0
    first = True
    for digit, count in iter_runs(word):
        if first:
            if not 0 <= digit < int(base) or not (digit & 1):
                raise ValueError((base, digit))
            first = False
        if digit == sentinel:
            shift = (shift + (count % order) * (bits % order)) % order
            continue
        local = v2_positive(3 * digit + 1)
        if local >= bits:
            raise AssertionError((base, digit, local, sentinel))
        return CollatzRadialCharacter(order, shift + local)
    # A finite all-sentinel word represents (base**q-1)/3 and therefore
    # 3*n+1 == base**q exactly.
    return CollatzRadialCharacter(order, shift)


def collatz_radial_characters_word(
    word: CanonicalWord,
    orders: Iterable[int],
    *,
    base: int = 4,
) -> tuple[CollatzRadialCharacter, ...]:
    """Answer many cyclic observers from one LCM-order source projection."""
    requested = tuple(orders)
    if any(type(order) is not int for order in requested):
        raise TypeError("Collatz radial projections require exact orders")
    if any(order <= 0 for order in requested):
        raise ValueError(requested)
    if not requested:
        return ()
    master_order = 1
    for order in requested:
        master_order = lcm(master_order, order)
    master = collatz_radial_character_word(word, master_order, base=base)
    return tuple(master.quotient(order) for order in requested)


def collatz_character_period(order: int, *, base: int = 4) -> int:
    """Sentinel-run period relevant to ``k mod order``.

    Useful to canonicalize a long sentinel count before any observer lookup.
    """
    if type(order) is not int:
        raise TypeError("Collatz character periods require exact orders")
    bits = power4_radix_bits(base)
    if order <= 0:
        raise ValueError(order)
    return order // gcd(order, bits)


__all__ = [
    "CollatzGrowthCharacter",
    "CollatzRadialCharacter",
    "collatz_character_period",
    "collatz_growth_character_value",
    "collatz_growth_character_word",
    "collatz_radial_character_value",
    "collatz_radial_character_word",
    "collatz_radial_characters_word",
]
