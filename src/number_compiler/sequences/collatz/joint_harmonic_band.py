"""Source-pointed XOR, cyclotomic, and primary valuation ports for Collatz."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.fields.integer_congruence import exact_modular_power
from number_compiler.arithmetic.fields.two_adic import v2_positive

_TWO_ODD_POINT_ISSUER = object()


@dataclass(frozen=True, slots=True)
class TwoOddHarmonicBandId:
    """Source-free identity of the centered two-odd affine action."""

    normalized_odd_symbols: int = 2
    centered_gain: int = 9
    dyadic_denominator_power: int = 2


_TWO_ODD_HARMONIC_BAND_ID = TwoOddHarmonicBandId()


@dataclass(frozen=True, slots=True)
class TwoOddHarmonicBand:
    """Source-free action for one normalized two-odd block ``11``.

    For ``z = x + 1``, the block acts by ``z -> 9*z/4``. Its pointed
    projections share one issued inlet. The mod-7 period never authorizes
    repetitions; physical admission comes from pointed dyadic headroom.
    """

    @property
    def semantic_key(self) -> TwoOddHarmonicBandId:
        """Return the stable action identity, excluding source and phase."""
        return _TWO_ODD_HARMONIC_BAND_ID

    @staticmethod
    def xor_carry_cell(source_bit: int, carry: int) -> tuple[int, int]:
        """One exact binary cell of ``3*x+1`` with a two-bit carry state."""
        if type(source_bit) is not int or source_bit not in (0, 1):
            raise ValueError("XOR source input must be a binary digit")
        if type(carry) is not int or carry not in (0, 1, 2):
            raise ValueError("XOR carry input must belong to {0, 1, 2}")
        total = 3 * source_bit + carry
        return source_bit ^ (carry & 1), total // 2

    @property
    def first_normalized_xor_parity(self) -> int:
        """Base case from the exact low two source bits and incoming ``+1``."""
        first, carry = self.xor_carry_cell(1, 1)
        second, next_carry = self.xor_carry_cell(1, carry)
        if (first, carry, next_carry) != (0, 2, 2):
            raise AssertionError("fixed-inlet XOR/carry base case is invalid")
        return second

    def point(self, source: int) -> TwoOddHarmonicPoint:
        if type(source) is not int or source <= 0 or (source & 3) != 3:
            raise ValueError(
                "two-odd harmonic action requires a positive 3 mod 4 source"
            )
        center = source + 1
        remaining = center
        v3_center = 0
        while remaining % 3 == 0:
            remaining //= 3
            v3_center += 1
        remaining = center
        v5_center = 0
        while remaining % 5 == 0:
            remaining //= 5
            v5_center += 1
        return _issue_two_odd_harmonic_point(
            v2_positive(center),
            v3_center,
            center % 7,
            source % 5,
            v5_center,
            center % 25,
        )

    def point_zero_tail_free_3_border(self, source: int) -> TwoOddHarmonicPoint:
        """Issue a zero-v3/zero-v5 inlet from its exact low residues.

        An odd source with ``source % 6 != 5`` has ``v3(source + 1) = 0``;
        a 3-ending source has ``v5(source + 1) = 0``. This avoids repeated
        small-prime valuation scans on the production admission path.
        """
        if (
            type(source) is not int
            or source <= 0
            or source % 10 != 3
            or source % 6 == 5
            or (source & 3) != 3
        ):
            raise ValueError("zero-tail-free harmonic inlet lacks its source guard")
        center = source + 1
        return _issue_two_odd_harmonic_point(
            v2_positive(center),
            0,
            center % 7,
            source % 5,
            0,
            center % 25,
        )


@dataclass(frozen=True, slots=True, init=False)
class TwoOddHarmonicPoint:
    """Sealed projections; source and physical endpoint authority stays upstream."""

    v2_center: int
    v3_center: int
    phase7: int
    phase5: int
    v5_center: int
    phase25: int
    _issuer: object = field(default=None, repr=False, compare=False)
    _issued_snapshot: tuple[int, ...] = field(default=(), repr=False, compare=False)

    def __init__(
        self,
        v2_center: int,
        v3_center: int,
        phase7: int,
        phase5: int,
        v5_center: int,
        phase25: int,
        *,
        _issuer: object | None = None,
    ) -> None:
        coordinates = (
            v2_center,
            v3_center,
            phase7,
            phase5,
            v5_center,
            phase25,
        )
        if _issuer is not _TWO_ODD_POINT_ISSUER:
            raise TypeError("harmonic band bindings require their source issuer")
        if (
            any(type(value) is not int for value in coordinates)
            or v2_center < 0
            or v3_center < 0
            or v5_center < 0
            or not 0 <= phase7 < 7
            or not 0 <= phase5 < 5
            or not 0 <= phase25 < 25
            or (phase25 - 1) % 5 != phase5
            or (v5_center > 0) != (phase25 % 5 == 0)
        ):
            raise ValueError("invalid pointed harmonic band")
        for name, value in zip(
            (
                "v2_center",
                "v3_center",
                "phase7",
                "phase5",
                "v5_center",
                "phase25",
            ),
            coordinates,
            strict=True,
        ):
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_issuer", _TWO_ODD_POINT_ISSUER)
        object.__setattr__(self, "_issued_snapshot", coordinates)

    @classmethod
    def _issued(
        cls,
        v2_center: int,
        v3_center: int,
        phase7: int,
        phase5: int,
        v5_center: int,
        phase25: int,
    ) -> TwoOddHarmonicPoint:
        return cls(
            v2_center,
            v3_center,
            phase7,
            phase5,
            v5_center,
            phase25,
            _issuer=_TWO_ODD_POINT_ISSUER,
        )

    def _require_issued(self) -> None:
        snapshot = (
            self.v2_center,
            self.v3_center,
            self.phase7,
            self.phase5,
            self.v5_center,
            self.phase25,
        )
        if (
            type(self) is not TwoOddHarmonicPoint
            or self._issuer is not _TWO_ODD_POINT_ISSUER
            or self._issued_snapshot != snapshot
        ):
            raise ValueError("pointed harmonic band seal changed")

    @property
    def semantic_key(self) -> TwoOddHarmonicBandId:
        """Return the source-free action identity, excluding occurrence data."""
        self._require_issued()
        return TWO_ODD_HARMONIC_BAND.semantic_key

    @property
    def cyclotomic_period(self) -> int:
        self._require_issued()
        return 1 if self.phase7 == 0 else 3

    @property
    def full_block_capacity(self) -> int:
        self._require_issued()
        return self.v2_center // 2

    @property
    def trailing_base6_fives(self) -> int:
        self._require_issued()
        return min(self.v2_center, self.v3_center)

    @property
    def border_digit(self) -> int:
        self._require_issued()
        parity = int(self.v2_center > 0)
        return self.phase5 if self.phase5 % 2 == parity else self.phase5 + 5

    @property
    def return_to_three_capacity(self) -> int:
        self._require_issued()
        if self.border_digit != 3:
            return 0
        return max(0, (self.v2_center - 1) // 2)

    def advance(self, blocks: int) -> TwoOddHarmonicPoint:
        self._require_issued()
        if type(blocks) is not int or not 0 <= blocks <= self.full_block_capacity:
            raise ValueError("two-odd harmonic power exceeds the 2-adic source guard")
        return self._issued(
            self.v2_center - 2 * blocks,
            self.v3_center + 2 * blocks,
            self.phase7 * pow(4, blocks, 7) % 7,
            self.phase5,
            self.v5_center,
            self.phase25 * pow(21, blocks, 25) % 25,
        )

    def certify_source(self, source: int) -> None:
        self._require_issued()
        if TWO_ODD_HARMONIC_BAND.point(source) != self:
            raise ValueError("foreign source for the pointed harmonic band")

    def endpoint(self, source: int, blocks: int) -> int:
        self.certify_source(source)
        self.advance(blocks)
        gain: int = 9**blocks
        return gain * ((source + 1) >> (2 * blocks)) - 1

    def pointed_period5(self, precision: int) -> int:
        self._require_issued()
        if type(precision) is not int or not 1 <= precision <= 2048:
            raise ValueError("5-adic precision must be in 1..2048")
        period: int = 5 ** max(0, precision - self.v5_center - 1)
        return period

    def next_period5_lift(self, precision: int) -> int:
        self._require_issued()
        if type(precision) is not int or not 1 <= precision < 2048:
            raise ValueError("5-adic lift precision must be in 1..2047")
        return self.pointed_period5(precision + 1) // self.pointed_period5(precision)

    def joint_cyclotomic_period(self, precision5: int) -> int:
        """Return the independent mod-7 / centered 5-adic return period."""
        self._require_issued()
        if type(precision5) is not int or not 1 <= precision5 <= 2048:
            raise ValueError("5-adic precision must be in 1..2048")
        # The periods are powers of five times one or three, hence coprime.
        return self.cyclotomic_period * self.pointed_period5(precision5)

    def phase5_power(self, source: int, precision: int, blocks: int) -> int:
        self.certify_source(source)
        self.advance(blocks)
        if type(precision) is not int or not 1 <= precision <= 2048:
            raise ValueError("5-adic precision must be in 1..2048")
        modulus: int = 5**precision
        inverse_four = (3 * modulus + 1) // 4
        gain: int = 9 * inverse_four % modulus
        phase = (source + 1) % modulus
        return phase * exact_modular_power(gain, blocks, modulus) % modulus

    def v5_return_defect(self, blocks: int) -> int:
        self._require_issued()
        if type(blocks) is not int or not 1 <= blocks <= self.full_block_capacity:
            raise ValueError("return defect requires an admitted nonzero block count")
        reduced = blocks
        exponent = 0
        while reduced % 5 == 0:
            reduced //= 5
            exponent += 1
        return self.v5_center + 1 + exponent

    def v2_return_defect(self, blocks: int) -> int:
        self._require_issued()
        if type(blocks) is not int or not 1 <= blocks <= self.full_block_capacity:
            raise ValueError("return defect requires an admitted nonzero block count")
        return self.v2_center - 2 * blocks

    def parity_after_odd_steps(self, steps: int) -> int:
        self._require_issued()
        if type(steps) is not int or not 0 <= steps <= self.v2_center:
            raise ValueError("XOR parity demand exceeds all-odd headroom")
        if steps == 1:
            return TWO_ODD_HARMONIC_BAND.first_normalized_xor_parity
        return int(self.v2_center > steps)

    def base6_five_band_after_odd_steps(self, steps: int) -> int:
        self.parity_after_odd_steps(steps)
        return min(self.v2_center - steps, self.v3_center + steps)

    def harmonic9_innovation(self, steps: int, incoming: int = 0) -> int:
        self.parity_after_odd_steps(steps)
        if type(incoming) is not int:
            raise TypeError("harmonic input must be an integer")
        gain = pow(6, steps, 9)
        return (gain * incoming + gain - 1) % 9

    def odd_prefix_ports(self, steps: int) -> tuple[int, int, int, int, int]:
        self._require_issued()
        parity = self.parity_after_odd_steps(steps)
        phase5 = (self.phase5 + 1) * pow(4, steps, 5) % 5
        residue5 = (phase5 - 1) % 5
        border = residue5 if residue5 % 2 == parity else residue5 + 5
        phase7 = self.phase7 * pow(5, steps, 7) % 7
        phase25 = self.phase25 * pow(14, steps, 25) % 25
        return (
            parity,
            border,
            phase7,
            phase25,
            self.harmonic9_innovation(steps),
        )


def _issue_two_odd_harmonic_point(
    v2_center: int,
    v3_center: int,
    phase7: int,
    phase5: int,
    v5_center: int,
    phase25: int,
) -> TwoOddHarmonicPoint:
    """Build a checked pointed projection through its validating constructor."""
    return TwoOddHarmonicPoint(
        v2_center,
        v3_center,
        phase7,
        phase5,
        v5_center,
        phase25,
        _issuer=_TWO_ODD_POINT_ISSUER,
    )


TWO_ODD_HARMONIC_BAND = TwoOddHarmonicBand()


__all__ = [
    "TWO_ODD_HARMONIC_BAND",
    "TwoOddHarmonicBand",
    "TwoOddHarmonicBandId",
    "TwoOddHarmonicPoint",
]
