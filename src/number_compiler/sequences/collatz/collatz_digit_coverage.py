"""Exact, position-aware base-6 coverage for Collatz source cylinders.

The outer interval certifies a common leading word; the complete CRT stride
certifies a common low word. The resulting coverage is a *proof of positions*,
not a guessed all-5 interior or a period inferred from a Sturmian rotation.
Uncovered positions remain explicit and cannot be used for macro admission.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.fields.radix import radix_width
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.collatz_two_sided_ring import (
        CollatzTwoSidedCylinder,
    )


def _charge_operand_bits(ledger: ResourceLedger | None, *values: int) -> None:
    if ledger is not None:
        ledger.bump(
            _collatz_keys.COLLATZ_RADIX6_COVERAGE_OPERAND_BITS,
            sum(value.bit_length() for value in values),
        )


def _power_six(exponent: int, ledger: ResourceLedger | None) -> int:
    _charge_operand_bits(ledger, 6, exponent)
    return cast(int, pow(6, exponent))


@dataclass(frozen=True, slots=True)
class Radix6DigitCoverage:
    """Source-wide digit certificate with contiguous high and low bands.

    Positions are zero-based from the least significant base-6 digit. The low
    region includes every proved all-5 suffix digit, while an unknown gap is
    **never** silently filled by that suffix's frequency or the radial clock.
    """

    width: int
    high_digits: int
    high_word: int
    low_digits: int
    low_word: int
    forced_five_suffix: int
    alternatives: int
    proven_value: int | None

    @property
    def uncovered(self) -> tuple[int, int] | None:
        start = self.low_digits
        stop = self.width - self.high_digits
        return (start, stop) if start < stop else None

    @property
    def complete(self) -> bool:
        return self.uncovered is None

    def digit_at(self, position: int) -> int | None:
        if type(position) is not int or not 0 <= position < self.width:
            raise ValueError("base-6 position lies outside certified width")
        if position < self.low_digits:
            place = cast(int, pow(6, position))
            return (self.low_word // place) % 6
        if position >= self.width - self.high_digits:
            place = cast(int, pow(6, position - (self.width - self.high_digits)))
            return (self.high_word // place) % 6
        return None

    def observation(self) -> dict[str, object]:
        return {
            "base": 6,
            "width": self.width,
            "high_interval": (self.width - self.high_digits, self.width),
            "high_word": self.high_word,
            "low_interval": (0, self.low_digits),
            "low_word": self.low_word,
            "forced_digit_five_interval": (
                (0, self.forced_five_suffix) if self.forced_five_suffix else None
            ),
            "uncovered_interval": self.uncovered,
            "complete": self.complete,
            "source_alternatives": self.alternatives,
            "proved_integer": self.proven_value,
            "authority": "exact upper interval and full source CRT stride",
        }


def certify_radix6_coverage(
    cylinder: CollatzTwoSidedCylinder,
    *,
    max_leading_digits: int | None = None,
    max_trailing_digits: int | None = None,
    ledger: ResourceLedger | None = None,
) -> Radix6DigitCoverage | None:
    """Certify every reported digit for *all* source alternatives.

    An exact source-wide width is required. The upper band is derived from
    the extreme possible values; the low band is derived only from complete
    powers of six dividing the *full* source stride. Even a singleton retains
    those proof depths rather than implicitly reading its missing interior.
    """
    if max_leading_digits is not None and (
        type(max_leading_digits) is not int or max_leading_digits < 0
    ):
        raise ValueError("invalid upper digit budget")
    if max_trailing_digits is not None and (
        type(max_trailing_digits) is not int or max_trailing_digits < 0
    ):
        raise ValueError("invalid lower digit budget")
    if ledger is not None and type(ledger) is not ResourceLedger:
        raise TypeError("radix-6 coverage accounting needs a query ledger")
    if ledger is not None:
        ledger.bump(_collatz_keys.COLLATZ_RADIX6_COVERAGE_EVALUATIONS)
    _charge_operand_bits(
        ledger,
        cylinder.lower,
        cylinder.upper,
        cylinder.residue,
        cylinder.modulus,
    )
    first, last = cylinder.first, cylinder.last
    charge_width_bits: Callable[[int], None] | None = (
        None
        if ledger is None
        else lambda bits: ledger.bump(
            _collatz_keys.COLLATZ_RADIX6_COVERAGE_OPERAND_BITS, bits
        )
    )
    width = radix_width(first, 6, charge_bits=charge_width_bits)
    last_width = radix_width(last, 6, charge_bits=charge_width_bits)
    if last_width != width:
        return None
    high_cap = (
        min(width, max_leading_digits) if max_leading_digits is not None else width
    )
    lo, hi = 0, high_cap + 1
    while lo + 1 < hi:
        _charge_operand_bits(ledger, lo, hi, 1)
        mid = (lo + hi) >> 1
        place = _power_six(width - mid, ledger)
        _charge_operand_bits(ledger, first, place, last)
        first_prefix = first // place
        last_prefix = last // place
        _charge_operand_bits(ledger, first_prefix, last_prefix)
        if first_prefix == last_prefix:
            lo = mid
        else:
            hi = mid
    high = lo
    if high:
        high_place = _power_six(width - high, ledger)
        _charge_operand_bits(ledger, first, high_place)
        high_word = first // high_place
    else:
        high_word = 0
    low_cap = (
        min(width, max_trailing_digits) if max_trailing_digits is not None else width
    )
    lo, hi = 0, low_cap + 1
    while lo + 1 < hi:
        _charge_operand_bits(ledger, lo, hi, 1)
        mid = (lo + hi) >> 1
        place = _power_six(mid, ledger)
        _charge_operand_bits(ledger, cylinder.modulus, place)
        if cylinder.modulus % place == 0:
            lo = mid
        else:
            hi = mid
    low = lo
    if low:
        low_place = _power_six(low, ledger)
        _charge_operand_bits(ledger, cylinder.residue, low_place)
        low_word = cylinder.residue % low_place
    else:
        low_word = 0
    all_fives = 0
    residue_plus_one = low_word + 1
    _charge_operand_bits(ledger, low_word, 1)
    while all_fives < low:
        _charge_operand_bits(ledger, residue_plus_one, 6)
        if residue_plus_one % 6 != 0:
            break
        _charge_operand_bits(ledger, residue_plus_one, 6)
        all_fives += 1
        residue_plus_one //= 6
    proved = None
    if low + high >= width:
        # The overlap is already consistent because the extremal source lies
        # inside both certificates; verify reconstruction and uniqueness.
        missing_from_high = width - high
        low_mask = _power_six(missing_from_high, ledger)
        _charge_operand_bits(ledger, high_word, low_mask, low_word)
        candidate = high_word * low_mask + low_word % low_mask
        _charge_operand_bits(ledger, cylinder.count, candidate, cylinder.first)
        if cylinder.count != 1 or candidate != cylinder.first:
            raise ArithmeticError("complete digit bands disagree with source cylinder")
        proved = candidate
    return Radix6DigitCoverage(
        width, high, high_word, low, low_word, all_fives, cylinder.count, proved
    )


__all__ = ("Radix6DigitCoverage", "certify_radix6_coverage")
