"""Compact source-bound descriptor for the special transverse holonomy.

For an admitted special candidate every possible least prime divisor belongs
to ``q_m = 1 + stride*m``.  The complete transverse observer is the product of
those atoms through the square-root frontier.  This module represents that
frontier and its demanded unit/annihilator observation without evaluating the
product.

The distinction is deliberate.  A balanced tree for the interval product has
logarithmic depth but still evaluates every atom and performs one fewer ring
multiplication.  Production therefore publishes an unresolved compact
pullback.  The canonical enumerative differential remains research-only in
``devtools.experiments.power_numbers.special_transverse_jet``.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.sequences.power_numbers.admission import (
    require_special_candidate_budget,
)
from number_compiler.sequences.power_numbers.numbers import (
    mersenne_exponent_is_prime,
)


@dataclass(frozen=True, slots=True)
class SpecialTransverseWindow:
    """Exact symbolic set of admitted slots below the square-root frontier."""

    family: str
    parameter: int
    stride: int

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if type(self.parameter) is not int or type(self.stride) is not int:
            raise TypeError("transverse window parameters must be exact integers")
        if self.parameter < 0 or self.stride < 1:
            raise ValueError((self.parameter, self.stride))
        if self.family == "fermat":
            canonical = (
                self.parameter >= 2
                and self.stride & (self.stride - 1) == 0
                and self.stride.bit_length() == self.parameter + 3
            )
        else:
            canonical = (
                self.parameter >= 3
                and bool(self.parameter & 1)
                and self.parameter < 1 << 64
                and mersenne_exponent_is_prime(self.parameter)
                and self.stride == 2 * self.parameter
            )
        if not canonical:
            raise ValueError("transverse window requires its canonical progression")

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-transverse-sqrt-window",
            self.family,
            self.parameter,
            self.stride,
        )

    def slot_value(self, slot: int) -> int:
        if type(slot) is not int:
            raise TypeError("transverse slot must be an exact integer")
        if slot < 1:
            raise ValueError(slot)
        return 1 + self.stride * slot

    def contains(self, slot: int) -> bool:
        """Decide ``q_slot <= floor(sqrt(N))`` without constructing ``N``."""
        q = self.slot_value(slot)
        square = q * q
        square_bits = square.bit_length()
        candidate_power = (
            1 << self.parameter if self.family == "fermat" else self.parameter
        )
        # Mersenne: q^2 <= 2^p-1 exactly when q^2 has at most p bits.
        if self.family == "mersenne":
            return square_bits <= candidate_power
        # Fermat: compare q^2 with 2^(2^n)+1.  Only the equality boundary
        # needs more than a bit-length comparison, and it can be recognized
        # without constructing the candidate.
        if square_bits <= candidate_power:
            return True
        if square_bits > candidate_power + 1:
            return False
        below = square - 1
        return (
            below > 0
            and below & (below - 1) == 0
            and below.bit_length() - 1 == candidate_power
        )

    def exceeds(self, maximum_slots: int) -> bool:
        """Return whether the exact window has more than ``maximum_slots``."""
        if type(maximum_slots) is not int or maximum_slots < 0:
            raise ValueError("maximum_slots must be a nonnegative exact integer")
        return self.contains(maximum_slots + 1)

    def materialize(self, *, maximum_slots: int) -> int:
        """Return the exact slot count only after a caller supplies a hard cap."""
        if self.exceeds(maximum_slots):
            raise ValueError("transverse window exceeds maximum_slots")
        low, high = 0, maximum_slots
        while low < high:
            middle = (low + high + 1) // 2
            if self.contains(middle):
                low = middle
            else:
                high = middle - 1
        return low


@dataclass(frozen=True, slots=True)
class CompactTransverseHolonomyPullback:
    """One compact request for the unit/annihilator of the whole holonomy.

    ``unit`` and ``annihilator`` remain absent until a candidate-derived
    evaluator supplies them.  The zero work counters make it impossible to
    mistake this descriptor for an evaluated interval product.
    """

    family: str
    parameter: int
    modulus_bits: int
    window: SpecialTransverseWindow
    unit: bool | None = field(default=None, init=False)
    annihilator: int | None = field(default=None, init=False)
    atom_evaluations: int = 0
    product_multiplications: int = 0
    factor_enumeration: int = 0
    candidate_derived: bool = True

    def __post_init__(self) -> None:
        if (
            self.family != self.window.family
            or self.parameter != self.window.parameter
            or self.modulus_bits < 1
        ):
            raise ValueError((self.family, self.parameter, self.window))
        if any(
            value
            for value in (
                self.atom_evaluations,
                self.product_multiplications,
                self.factor_enumeration,
            )
        ):
            raise ValueError("compact transverse pullback cannot hide product work")
        if self.unit is not None or self.annihilator is not None:
            raise ValueError(
                "compact descriptor cannot issue a unit or annihilator witness"
            )

    @property
    def decided(self) -> bool:
        return self.unit is not None

    @property
    def method(self) -> str:
        return "transverse-holonomy-pullback-unresolved"

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "compact-transverse-holonomy-pullback",
            self.family,
            self.parameter,
            self.modulus_bits,
            self.window.canonical_key,
            self.unit,
            self.annihilator,
        )


def build_compact_transverse_pullback(
    family: str,
    parameter: int,
    *,
    max_candidate_bits: int = 1_000_000,
) -> CompactTransverseHolonomyPullback:
    """Build the correct candidate-derived request without lowering its window."""
    require_special_candidate_budget(family, parameter, max_candidate_bits)
    if family == "fermat":
        if parameter < 2:
            raise ValueError("Fermat transverse progression requires n >= 2")
        stride = 1 << (parameter + 2)
        modulus_bits = (1 << parameter) + 1
    elif family == "mersenne":
        if parameter < 3 or not (parameter & 1):
            raise ValueError("Mersenne transverse progression requires odd p >= 3")
        if parameter >= 1 << 64 or not mersenne_exponent_is_prime(parameter):
            raise ValueError("Mersenne transverse progression requires prime p")
        stride = 2 * parameter
        modulus_bits = parameter
    else:
        raise ValueError(family)
    return CompactTransverseHolonomyPullback(
        family,
        parameter,
        modulus_bits,
        SpecialTransverseWindow(family, parameter, stride),
    )


__all__ = [
    "CompactTransverseHolonomyPullback",
    "SpecialTransverseWindow",
    "build_compact_transverse_pullback",
]
