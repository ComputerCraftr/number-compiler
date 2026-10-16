"""Source-bound upper/lower carry coordinate for 6305 border returns.

For an admitted three-ending source ``x = 10*q + 3``, multiplication emits
the units digit zero and carry one, so ``3*x + 1 = 10*(3*q + 1)``.  Keeping
the upper numerator ``3*q + 1`` across returns avoids reconstructing it from
each complete endpoint.  The cursor describes a finite selected return; it
does not authorize an unselected future parity word.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.homogeneous_growth import (
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.position_cycle_harmonics import (
        PositionHarmonicSpectrum,
    )


def next_6305_upper_numerator(upper_odd: int) -> int | None:
    """Return the next three-border numerator when the selected exit is 3."""
    if type(upper_odd) is not int or upper_odd <= 0 or upper_odd & 1 == 0:
        raise ValueError("6305 upper odd coordinate must be a positive odd integer")
    if upper_odd & 3 != 3:
        return None
    return (9 * upper_odd + 1) >> 2


@dataclass(frozen=True, slots=True)
class Border6305CarryCylinder:
    """Upper 2-adic numerator attached to the forced lower decimal carry."""

    upper_numerator: int

    def __post_init__(self) -> None:
        if type(self.upper_numerator) is not int or self.upper_numerator <= 0:
            raise ValueError("6305 upper numerator must be a positive integer")

    @classmethod
    def from_three_digit(cls, source: int) -> Border6305CarryCylinder:
        if type(source) is not int or source <= 0 or source % 10 != 3:
            raise ValueError("6305 carry requires an admitted three-ending source")
        return cls(3 * ((source - 3) // 10) + 1)

    @property
    def zero_tail(self) -> int:
        return v2_positive(self.upper_numerator)

    @property
    def upper_odd(self) -> int:
        return self.upper_numerator >> self.zero_tail

    @property
    def endpoint(self) -> int:
        return (15 * self.upper_odd + 1) >> 1

    @property
    def endpoint_digit(self) -> int:
        return 3 if self.upper_odd & 3 == 3 else 8

    @property
    def endpoint_residue20(self) -> int:
        return ((15 * (self.upper_odd & 7) + 1) >> 1) % 20

    @property
    def zero_tail_free_return_count(self) -> int:
        """Count consecutive zero-tail 3->3 returns from this cylinder.

        This is an exact prefix length of the already selected 6305 border
        recurrence. It does not certify a later source selector or extend the
        finite action beyond the returned count.
        """
        if self.zero_tail != 0:
            return 0
        return v2_positive(5 * self.upper_odd + 1) // 2

    @property
    def exit_to_nine(self) -> bool:
        return self.upper_odd & 7 == 5

    @property
    def affine_binary_correction(self) -> int:
        """Correction after ``floor(9*x / 2**(j+2))``."""
        return 2 if self.zero_tail == 0 else 1

    @property
    def radial_scale(self) -> HomogeneousGrowthScale:
        """Homogeneous multiplier for this single admitted return."""
        return HomogeneousGrowthScale(2, self.zero_tail + 2)

    def source_congruence(self, upper_bits: int = 3) -> tuple[int, int]:
        """Recover the source cylinder from ``j`` and low bits of odd ``u``."""
        if type(upper_bits) is not int or upper_bits < 1:
            raise ValueError("upper odd cylinder needs at least one bit")
        exponent = self.zero_tail
        modulus_q = 1 << (exponent + upper_bits)
        low_odd = self.upper_odd & ((1 << upper_bits) - 1)
        q = ((low_odd << exponent) - 1) * pow(3, -1, modulus_q) % modulus_q
        modulus_x = 10 * modulus_q
        return (10 * q + 3) % modulus_x, modulus_x

    def next_return(self) -> Border6305CarryCylinder | None:
        numerator = next_6305_upper_numerator(self.upper_odd)
        return Border6305CarryCylinder(numerator) if numerator is not None else None

    def demanded_position_harmonics(
        self,
        repetitions: int,
        radix: int,
        position: int,
        *,
        walsh64: bool = False,
    ) -> PositionHarmonicSpectrum:
        """Read a fixed position over an admitted zero-tail-free 6305 word."""
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            ZeroTailFree6305Orbit,
        )

        if self.zero_tail != 0 or self.upper_numerator % 3 != 1:
            raise ValueError("position harmonic requires a valid zero-tail-free entry")
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("position harmonic extent must be nonnegative")
        source = 10 * ((self.upper_numerator - 1) // 3) + 3
        return ZeroTailFree6305Orbit(source, repetitions).spectrum(
            radix, position, walsh64=walsh64
        )

    def affine_pivot_mask(self, width: int = 64) -> int:
        """Bounded XOR mask for the exact +1/+2 affine endpoint correction."""
        if type(width) is not int or width < 0:
            raise ValueError("pivot width must be a nonnegative integer")
        if width == 0:
            return 0
        endpoint = self.endpoint
        if self.affine_binary_correction == 1:
            low = 0
            changed = v2_positive(endpoint) + 1
        else:
            low = 1
            changed = v2_positive(endpoint >> 1) + 1
        visible = min(changed, width - low)
        return ((1 << visible) - 1) << low


__all__ = ["Border6305CarryCylinder", "next_6305_upper_numerator"]
