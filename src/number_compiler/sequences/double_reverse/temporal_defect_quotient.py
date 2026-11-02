"""Exact normalized two-direction carry defect and finite suffix-clock algebra.

For a reverse-carry right pass followed by ordinary doubling, a normalized
word X has successor F(X).  When two successive right passes have exactly one
birth (g0 + g1 = 1), the four-physical-tick return is

    F(F(X)) = 160 X - 198 J,

with one *combined* carry word J whose decimal columns lie in {0,1,4,5}.
The two Boolean carry tapes can be recovered independently from each J column.

The source is a right suffix with a bounded left halo.  The second carry tape
is calculated by the first exact pass, NOT read as an independent input.  Only
finite, source-verified periods are reported: temporal powering of a supplied
innovation block is never mistaken for a proof that the seed repeats it.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power

from .temporal_alternating_carry import normalized_t_squared_suffix_trace

MAX_DEFECT_WIDTH = 96


def defect_modulus(width: int) -> int:
    """Return the exact ``2*10**width`` ring after enforcing CLI width bounds."""
    if type(width) is not int or not 1 <= width <= MAX_DEFECT_WIDTH:
        raise ValueError("defect ring width must be in 1..96")
    decimal_power = 1
    for _ in range(width):
        decimal_power *= 10
    return 2 * decimal_power


def _digits(value: tuple[int, ...]) -> int:
    v = 0
    for digit in value:
        if type(digit) is not int or not 0 <= digit <= 9:
            raise ValueError("carry defect requires decimal digits")
        v = 10 * v + digit
    return v


def _carry_mask(digits: tuple[int, ...]) -> int:
    value = 0
    for digit in digits:
        value = value * 10 + int(digit >= 5)
    return value


@dataclass(frozen=True, slots=True)
class DualDirectionalCarry:
    """Both actual carry emissions for one normalized T² update.

    The right observer reads the source even-frame digit thresholds. The left
    observer reads the newly produced odd-frame thresholds, transported into
    the reflected coordinate frame by reversing the bounded carry word.
    They are not independently supplied port programs. ``width`` refers to a
    local retained suffix; its mirror is not automatically a global prefix.
    """

    width: int
    right_mask: int
    left_mask: int
    left_mirror_mask: int

    @classmethod
    def from_passes(
        cls, source: tuple[int, ...], odd: tuple[int, ...], width: int
    ) -> DualDirectionalCarry:
        if type(width) is not int or width < 1:
            raise ValueError("directional carry width must be positive")
        if len(source) < width or len(odd) < width:
            raise ValueError("directional carry block missing its retained suffix")
        right = _carry_mask(source[-width:])
        left = _carry_mask(odd[-width:])
        mirror = int(str(left).zfill(width)[::-1])
        action = cls(width, right, left, mirror)
        action.verify()
        return action

    def verify(self) -> None:
        if type(self.width) is not int or self.width < 1:
            raise ValueError("invalid directional carry width")
        limit = 10**self.width
        if any(
            type(v) is not int
            or not 0 <= v < limit
            or any(c not in "01" for c in str(v).zfill(self.width))
            for v in (self.right_mask, self.left_mask, self.left_mirror_mask)
        ):
            raise ValueError("directional carry tapes are not Boolean")
        if self.left_mirror_mask != int(str(self.left_mask).zfill(self.width)[::-1]):
            raise ValueError("left-carry mirror transport mismatch")

    def ordered_right_bits(self) -> str:
        return str(self.right_mask).zfill(self.width)

    def ordered_left_bits(self) -> str:
        return str(self.left_mask).zfill(self.width)[::-1]


@dataclass(frozen=True, slots=True)
class FourSymbolDefect:
    """Two ordered carry masks and one exact width-bounded defect symbol word."""

    width: int
    first_growth: int
    second_growth: int
    first_carries: int
    second_carries: int
    combined_decimal: int
    combined_base5: int
    input_modulus: int
    output_modulus: int
    first_directional: DualDirectionalCarry
    second_directional: DualDirectionalCarry

    @property
    def modulus(self) -> int:
        return defect_modulus(self.width)

    def emission_digits(self) -> str:
        return str(self.combined_decimal).zfill(self.width)

    def base5_digits(self) -> str:
        return "".join(
            str(2 * (int(ch) // 4) + (int(ch) % 4)) for ch in self.emission_digits()
        )

    def aligned_left_carries(self) -> tuple[int, int]:
        """Two chronological LEFT-wave carry masks in the macro coordinate.

        The second mask loses one low-position digit in the no-birth phase,
        exactly as the established right-wave macro alignment does. The first
        mask is already in the source coordinate. Both remain independent
        output labels of the SAME authenticated two-pass transitions.
        """
        second = self.second_directional.left_mask
        if self.second_growth == 0:
            second //= 10
        return self.first_directional.left_mask, second

    def left_defect_decimal(self) -> int:
        """Complementary four-symbol LEFT-wave emission, not radial forcing."""
        a, b = self.aligned_left_carries()
        return 4 * a + b

    def left_mirrored_defect_decimal(self) -> int:
        """The same left-wave output seen in reversed bounded coordinates."""
        a, b = self.aligned_left_carries()
        return 4 * int(str(a).zfill(self.width)[::-1]) + int(
            str(b).zfill(self.width)[::-1]
        )

    def left_base5_digits(self) -> str:
        return "".join(
            str(2 * (int(ch) // 4) + (int(ch) % 4))
            for ch in str(self.left_defect_decimal()).zfill(self.width)
        )

    def verify(self) -> None:
        exact_integer_fields = (
            self.width,
            self.first_growth,
            self.second_growth,
            self.first_carries,
            self.second_carries,
            self.combined_decimal,
            self.combined_base5,
            self.input_modulus,
            self.output_modulus,
        )
        if (
            any(type(value) is not int for value in exact_integer_fields)
            or not 1 <= self.width <= MAX_DEFECT_WIDTH
            or self.first_growth not in (0, 1)
            or self.second_growth not in (0, 1)
            or self.first_growth + self.second_growth != 1
        ):
            raise ValueError("invalid four-symbol temporal defect")
        decimal_limit = 10**self.width
        if (
            not 0 <= self.first_carries < decimal_limit
            or not 0 <= self.second_carries < decimal_limit
            or not 0 <= self.combined_decimal < decimal_limit
            or not 0 <= self.combined_base5 < 5**self.width
            or not 0 <= self.input_modulus < self.modulus
            or not 0 <= self.output_modulus < self.modulus
        ):
            raise ValueError("four-symbol defect field is outside its width")
        if (
            type(self.first_directional) is not DualDirectionalCarry
            or type(self.second_directional) is not DualDirectionalCarry
        ):
            raise ValueError(
                "combined defect must retain both physical carry directions"
            )
        self.first_directional.verify()
        self.second_directional.verify()
        if self.first_directional.width != self.width:
            raise ValueError("first directional carry width mismatch")
        if self.second_directional.width != self.width + (1 - self.second_growth):
            raise ValueError("second directional carry width mismatch")
        if self.first_directional.right_mask != self.first_carries:
            raise ValueError("first-direction carry mask not source-aligned")
        second_right_aligned = self.second_directional.right_mask
        if self.second_growth == 0:
            second_right_aligned //= 10
        if second_right_aligned != self.second_carries:
            raise ValueError("second-direction carry mask not birth-aligned")
        symbols = self.emission_digits()
        if any(c not in "0145" for c in symbols):
            raise ValueError("defect is not a four-symbol carry word")
        if self.combined_decimal != 4 * self.first_carries + self.second_carries:
            raise ValueError("defect column does not match its carry tapes")
        if self.combined_base5 != _base5_from_decimal_word(
            self.combined_decimal, self.width
        ):
            raise ValueError("defect base-five decoding mismatch")
        for value in (self.left_defect_decimal(), self.left_mirrored_defect_decimal()):
            if value >= 10**self.width or any(
                c not in "0145" for c in str(value).zfill(self.width)
            ):
                raise ValueError("left-wave combined defect is not four-symbol")
        if int(self.left_base5_digits(), 5) != _base5_from_decimal_word(
            self.left_defect_decimal(), self.width
        ):
            raise ValueError("left-wave base-five output mismatch")
        if (
            160 * self.input_modulus - 198 * self.combined_decimal
        ) % self.modulus != self.output_modulus:
            raise ValueError("defect forcing disagrees with both exact doublings")


def _base5_from_decimal_word(value: int, width: int) -> int:
    out = 0
    for symbol in str(value).zfill(width):
        digit = int(symbol)
        if digit not in (0, 1, 4, 5):
            raise ValueError("combined defect has an invalid column")
        out = 5 * out + 2 * (digit // 4) + digit % 4
    return out


def defect_and_successor_from_normalized_suffix(
    source_suffix: tuple[int, ...], width: int
) -> tuple[FourSymbolDefect, tuple[int, ...]]:
    """Compute one exact defect and the full two-pass successor source.

    The complete left causal halo is retained for the following sample; no
    second evaluation of the two temporal steps is necessary. All issued
    carry/defect fields are still projections of the same source.

    Compute one exact four-generation defect from ONE source suffix.

    The suffix must contain at least ``width+4`` low decimal positions (pad
    missing high digits with zeros). Both time-directed carry scans are made
    locally, with no occurrence ID, independently supplied inlet or future
    oracle. The extra four positions cover the two successive radius-one
    stencil updates and the ``2*10**width`` modulus.
    """
    if type(width) is not int or not 1 <= width <= MAX_DEFECT_WIDTH:
        raise ValueError("defect width must be in 1..96")
    if type(source_suffix) is not tuple:
        raise TypeError("source suffix must be an immutable decimal tuple")
    _digits(source_suffix)
    if len(source_suffix) < width + 4:
        raise ValueError("defect source suffix is missing its left carry halo")
    source = source_suffix
    odd_first, first, g0 = normalized_t_squared_suffix_trace(source)
    odd_second, second, g1 = normalized_t_squared_suffix_trace(first)
    if g0 + g1 != 1:
        raise ValueError("source is not in a one-birth, four-generation macro phase")
    first_directional = DualDirectionalCarry.from_passes(source, odd_first, width)
    second_directional = DualDirectionalCarry.from_passes(
        first, odd_second, width + (1 - g1)
    )
    c0 = first_directional.right_mask
    c1 = (
        second_directional.right_mask // 10
        if g1 == 0
        else second_directional.right_mask
    )
    j = 4 * c0 + c1
    if j >= 10**width:
        raise AssertionError("four-symbol combined defect overflowed a column")
    m = 2 * 10**width
    defect = FourSymbolDefect(
        width=width,
        first_growth=g0,
        second_growth=g1,
        first_carries=c0,
        second_carries=c1,
        combined_decimal=j,
        combined_base5=_base5_from_decimal_word(j, width),
        input_modulus=_digits(source) % m,
        output_modulus=_digits(second) % m,
        first_directional=first_directional,
        second_directional=second_directional,
    )
    defect.verify()
    return defect, second


def defect_from_normalized_suffix(
    source_suffix: tuple[int, ...], width: int
) -> FourSymbolDefect:
    """Existing minimal-halo API, now projected from the shared action."""
    if type(source_suffix) is not tuple:
        raise TypeError("source suffix must be an immutable decimal tuple")
    return defect_and_successor_from_normalized_suffix(
        source_suffix[-(width + 4) :], width
    )[0]


@dataclass(frozen=True, slots=True)
class DefectAffineClock:
    """Finite phase-aligned temporal action, modulo 2*10^width.

    Composition uses (A2*A1, A2*B1+B2) for x -> A*x + B.
    The forcing is *signed*. A temporal power describes an externally proven
    repeat of this action; it does not certify that a source orbit repeats.
    """

    width: int
    steps: int
    multiplier: int
    forcing: int

    @property
    def modulus(self) -> int:
        return defect_modulus(self.width)

    @classmethod
    def identity(cls, width: int) -> DefectAffineClock:
        if type(width) is not int or not 1 <= width <= MAX_DEFECT_WIDTH:
            raise ValueError("invalid affine defect width")
        return cls(width, 0, 1, 0)

    @classmethod
    def from_defect(cls, defect: FourSymbolDefect) -> DefectAffineClock:
        defect.verify()
        m = defect.modulus
        return cls(defect.width, 1, 160 % m, (-198 * defect.combined_decimal) % m)

    def then(self, later: DefectAffineClock) -> DefectAffineClock:
        if type(later) is not DefectAffineClock or later.width != self.width:
            raise ValueError("cannot compose incompatible defect clocks")
        m = self.modulus
        return DefectAffineClock(
            self.width,
            self.steps + later.steps,
            (later.multiplier * self.multiplier) % m,
            (later.multiplier * self.forcing + later.forcing) % m,
        )

    def power(self, repetitions: int) -> DefectAffineClock:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("invalid temporal repeat count")
        return binary_power(
            self,
            repetitions,
            identity=DefectAffineClock.identity(self.width),
            compose=lambda first, second: first.then(second),
        ).value

    def apply(self, source: int) -> int:
        if type(source) is not int or source < 0:
            raise ValueError("defect clock needs a nonnegative source residue")
        return (self.multiplier * source + self.forcing) % self.modulus


@dataclass(frozen=True, slots=True)
class FourSymbolSpatialQuotient:
    """Bounded canonical four-symbol spatial concatenation monoid.

    Both decimal and base-five encodings retain the same pair of Boolean
    carry bits at every position. Truncation is a *suffix* projection and not
    an assumed temporal Moore right congruence.
    """

    width: int
    length: int
    decimal: int
    base5: int

    @classmethod
    def identity(cls, width: int) -> FourSymbolSpatialQuotient:
        if type(width) is not int or width < 1:
            raise ValueError("invalid spatial quotient width")
        return cls(width, 0, 0, 0)

    @classmethod
    def from_digits(cls, digits: str, width: int) -> FourSymbolSpatialQuotient:
        if type(digits) is not str or any(c not in "0145" for c in digits):
            raise ValueError("spatial quotient accepts only carry-pair symbols")
        low = digits[-width:]
        return cls(
            width,
            len(digits),
            int(low or "0"),
            _base5_from_decimal_word(int(low or "0"), len(low)) if low else 0,
        )

    def then(self, higher: FourSymbolSpatialQuotient) -> FourSymbolSpatialQuotient:
        """Join low-position self then higher-position other."""
        if type(higher) is not FourSymbolSpatialQuotient or higher.width != self.width:
            raise ValueError("incompatible carry-quotient joins")
        w = self.width
        # Only the lowest w symbols are retained. The left operand denotes
        # the LOW positions, unlike normal MSB-first text concatenation.
        modulus10 = defect_modulus(w) // 2
        # 10**w / 2**w is exactly 5**w; both bounded moduli therefore share
        # the checked decimal power without introducing a second power loop.
        modulus5 = modulus10 >> w
        shift10 = pow(10, self.length, modulus10)
        shift5 = pow(5, self.length, modulus5)
        return FourSymbolSpatialQuotient(
            w,
            self.length + higher.length,
            (self.decimal + shift10 * higher.decimal) % modulus10,
            (self.base5 + shift5 * higher.base5) % modulus5,
        )

    def power(self, repetitions: int) -> FourSymbolSpatialQuotient:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("invalid compressed spatial repetition")
        return binary_power(
            self,
            repetitions,
            identity=FourSymbolSpatialQuotient.identity(self.width),
            compose=lambda first, second: first.then(second),
        ).value
