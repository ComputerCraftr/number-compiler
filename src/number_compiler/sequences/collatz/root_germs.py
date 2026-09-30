"""Root germs with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.program_word import (
    EMPTY,
    RunTraversalMetrics,
    SourceWord,
    drop_source_prefix,
    iter_runs,
    validate_source_word,
)
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.fields.two_adic import v2_nonzero
from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder


@dataclass(frozen=True, slots=True)
class RationalPadicRootMismatch:
    """First radix-4 mismatch against ``-constant / 3**denominator_power``."""

    denominator_power: int
    matched_quarters: int
    source_digit: int
    constant_at_mismatch: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.denominator_power,
                self.matched_quarters,
                self.source_digit,
                self.constant_at_mismatch,
            )
        ):
            raise TypeError("rational root mismatches require exact integers")
        if not 0 < self.denominator_power <= 40 or self.matched_quarters < 0:
            raise ValueError(self)
        if not 0 <= self.source_digit < 4:
            raise ValueError(self)
        if self.source_digit == self.root_digit:
            raise ValueError(self)

    @property
    def denominator(self) -> int:
        return int(3**self.denominator_power)

    @property
    def root_digit(self) -> int:
        return (-self.constant_at_mismatch * pow(self.denominator, -1, 4)) % 4

    @property
    def digit_v2(self) -> int:
        return v2_nonzero(self.source_digit - self.root_digit)

    @property
    def constant_after_root_digit(self) -> int:
        numerator = self.constant_at_mismatch + self.denominator * self.root_digit
        if numerator % 4:
            raise AssertionError((self, numerator))
        return numerator // 4

    @property
    def valuation_bits(self) -> int:
        return 2 * self.matched_quarters + self.digit_v2


@dataclass(frozen=True, slots=True)
class RationalPadicRootGerm:
    """Symbolic 2-adic root ``-c/3**h`` with radix-4 run acceleration.

    No period of length ``3**(h-1)`` is materialized.  For a constant source
    run of digit ``d``, compare the root with the infinite constant word
    ``...ddd_4 = -d/3``.  Their difference has 2-adic valuation

        v2(3*c - 3**h*d).

    Hence an arbitrarily long run is skipped by one valuation and one exact
    right shift.  This is the scalable replacement for the old hard-coded
    period-three boundary summary.
    """

    denominator_power: int
    constant: int

    def __post_init__(self) -> None:
        if type(self.denominator_power) is not int or type(self.constant) is not int:
            raise TypeError("rational root germs require exact integers")
        if not 0 < self.denominator_power <= 40:
            raise ValueError("rational root exponent must fit one 64-bit 3-adic limb")
        if abs(self.constant).bit_length() > 64:
            raise ValueError("rational root constant must fit one 64-bit limb")

    @property
    def denominator(self) -> int:
        return int(3**self.denominator_power)

    def root_residue(self, bits: int) -> int:
        if type(bits) is not int:
            raise TypeError("rational root precision must be an exact integer")
        if not 0 < bits <= 64:
            raise ValueError("rational root precision must fit one 64-bit limb")
        return HenselCylinder.from_root(
            bits, self.denominator_power, self.constant
        ).residue

    @property
    def radix4_digit(self) -> int:
        return (-self.constant * pow(self.denominator, -1, 4)) % 4

    def _advance_matching_run(
        self, digit: int, count: int
    ) -> tuple[int, RationalPadicRootGerm, RationalPadicRootMismatch | None]:
        if type(digit) is not int or type(count) is not int:
            raise TypeError("rational root runs require exact integers")
        if count < 0 or not 0 <= digit < 4:
            raise ValueError((digit, count))
        if count == 0:
            return 0, self, None
        p = self.denominator
        delta = 3 * self.constant - p * digit
        if delta == 0:
            return count, self, None
        agreement_bits = v2_nonzero(delta)
        quarters = min(count, agreement_bits // 2)
        fixed_constant = (p // 3) * digit
        diff = self.constant - fixed_constant
        if quarters:
            # Avoid constructing a 4**quarters mask.  Exact agreement already
            # says the difference contains at least 2*quarters low zero bits.
            if diff and v2_nonzero(diff) < 2 * quarters:
                raise AssertionError((self, digit, count, quarters, diff))
            current_constant = fixed_constant + (diff >> (2 * quarters))
        else:
            current_constant = self.constant
        current = RationalPadicRootGerm(self.denominator_power, current_constant)
        if quarters == count:
            return quarters, current, None
        root_digit = current.radix4_digit
        if root_digit == digit:
            raise AssertionError(
                (self, digit, count, agreement_bits, quarters, current)
            )
        e = digit - root_digit
        digit_v2 = v2_nonzero(e)
        if digit_v2 not in (0, 1) or 2 * quarters + digit_v2 != agreement_bits:
            raise AssertionError(
                (self, digit, root_digit, agreement_bits, quarters, digit_v2)
            )
        numerator = current.constant + p * root_digit
        if numerator % 4:
            raise AssertionError((current, root_digit, numerator))
        after = numerator // 4
        mismatch = RationalPadicRootMismatch(
            self.denominator_power,
            quarters,
            digit,
            current.constant,
        )
        if mismatch.constant_after_root_digit != after:
            raise AssertionError((mismatch, after))
        return quarters, current, mismatch

    def normalize_matching_prefix_word(
        self,
        word: SourceWord,
    ) -> tuple[int, RationalPadicRootGerm, SourceWord]:
        """Quotient the maximal root-matching low prefix before cache lookup.

        The returned quarter count is a coordinate action: it contributes
        ``2*quarters`` valuation bits but does not change the future angular
        boundary state.  A partial matching run is sliced without expanding
        its digits. Traversal stops at the first mismatch; the untouched
        high suffix retains its original source coordinates and subtree cover.
        Only the cut boundary is descended; no canonical suffix rebalance is
        performed. Leaves of at most eight runs retain bounded normalization.
        """
        validate_source_word(word)
        current = self
        consumed = 0
        for digit, count in iter_runs(word):
            matched, advanced, mismatch = current._advance_matching_run(digit, count)
            if mismatch is None:
                consumed += count
                current = advanced
                continue
            suffix = drop_source_prefix(word, consumed + matched)
            return consumed + matched, advanced, suffix
        return consumed, current, EMPTY

    def first_mismatch_word(
        self,
        word: SourceWord,
        *,
        metrics: RunTraversalMetrics | None = None,
    ) -> tuple[RationalPadicRootMismatch, SourceWord]:
        """Return the first mismatch and the unconsumed higher source suffix.

        The traversal is by canonical runs, never represented digits.  If every
        finite source digit agrees, the implicit high-zero extension supplies
        the mismatch.
        """
        validate_source_word(word, metrics=metrics)
        current = self
        consumed = 0
        runs = iter_runs(word) if metrics is None else iter_runs(word, metrics=metrics)
        for digit, count in runs:
            matched, advanced, mismatch = current._advance_matching_run(digit, count)
            if mismatch is None:
                consumed += count
                current = advanced
                continue
            suffix = drop_source_prefix(word, consumed + matched + 1, metrics=metrics)
            absolute = RationalPadicRootMismatch(
                mismatch.denominator_power,
                consumed + mismatch.matched_quarters,
                mismatch.source_digit,
                mismatch.constant_at_mismatch,
            )
            return absolute, suffix

        # Finite integer words are extended by high zeroes.  A nonzero rational
        # root must eventually disagree with that zero run.
        if current.constant == 0:
            raise ValueError(
                "source equals the zero rational root; valuation is infinite"
            )
        zeros = v2_nonzero(3 * current.constant) // 2 + 1
        matched, _advanced, mismatch = current._advance_matching_run(0, zeros)
        if mismatch is None:
            raise AssertionError((current, zeros, matched))
        absolute = RationalPadicRootMismatch(
            mismatch.denominator_power,
            consumed + mismatch.matched_quarters,
            mismatch.source_digit,
            mismatch.constant_at_mismatch,
        )
        return absolute, EMPTY

    def valuation_from_word(self, word: SourceWord) -> int:
        mismatch, _suffix = self.first_mismatch_word(word)
        return mismatch.valuation_bits

    def valuation_from_digits(self, digits: Sequence[int]) -> int:
        from number_compiler.arithmetic.automata.program_word import from_values

        values = tuple(digits)
        if any(type(value) is not int for value in values):
            raise TypeError("rational root digits must be exact integers")
        return self.valuation_from_word(from_values(values))

    def valuation_from_integer(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("rational root input must be an exact integer")
        if value < 0:
            raise ValueError(value)
        numerator = self.denominator * value + self.constant
        return v2_nonzero(numerator)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("rational-padic-root-germ", 3, self.denominator_power, self.constant)

    @property
    def description_bits(self) -> int:
        return bit_width(self.denominator_power) + bit_width(abs(self.constant)) + 2


@dataclass(frozen=True, slots=True)
class PadicAngularBoundaryGerm:
    """Normalized odd discrepancy after a rational-root first mismatch.

    If the remaining higher source suffix is ``M`` then

        (3**h * source + c) / 2**valuation = multiplier*M + offset.

    The affine coefficients are derived solely from the first mismatching digit
    and the advanced rational-root constant; no intermediate Collatz word is
    constructed.
    """

    denominator_power: int
    valuation: int
    offset: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.denominator_power,
                self.valuation,
                self.offset,
            )
        ):
            raise TypeError("p-adic angular boundary fields require exact integers")
        if not 0 < self.denominator_power <= 40 or self.valuation < 0:
            raise ValueError(self)
        if max(self.multiplier.bit_length(), abs(self.offset).bit_length()) > 128:
            raise ValueError("p-adic angular coefficients exceed two bounded limbs")

    @property
    def residual_phase(self) -> int:
        """Radix-four mismatch phase; matched quarters change valuation by two."""
        return self.valuation & 1

    @property
    def multiplier(self) -> int:
        """Derived angular scale, never an independent germ identity field."""
        denominator = int(3**self.denominator_power)
        return (4 * denominator) >> self.residual_phase

    @property
    def cocycle(self) -> AffineCocycle[int]:
        return AffineCocycle(self.multiplier, self.offset)

    @classmethod
    def from_mismatch(
        cls,
        root: RationalPadicRootGerm,
        mismatch: RationalPadicRootMismatch,
    ) -> PadicAngularBoundaryGerm:
        if root.denominator_power != mismatch.denominator_power:
            raise ValueError((root, mismatch))
        p = root.denominator
        e = mismatch.source_digit - mismatch.root_digit
        s = mismatch.digit_v2
        numerator = p * e + 4 * mismatch.constant_after_root_digit
        if numerator % (1 << s):
            raise AssertionError((root, mismatch, numerator))
        offset = numerator >> s
        result = cls(root.denominator_power, mismatch.valuation_bits, offset)
        if result.residual_phase != s:
            raise AssertionError((root, mismatch, result.residual_phase))
        return result

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "padic-angular-boundary-germ",
            self.denominator_power,
            self.valuation,
            self.offset,
        )
