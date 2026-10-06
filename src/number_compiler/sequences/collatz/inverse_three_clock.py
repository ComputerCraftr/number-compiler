"""Finite inverse-three clock views and radix-64 tangent skeletons.

At precision ``q`` the normalized coordinate is ``W_n = 3**(-n) x mod
2**q``.  The exact source prefix remains a spatial occurrence input; neither
it nor a finite evaluated ``W`` value enters the reusable clock identity.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.inverse_three_clock import (
    InverseThreeClock as _SharedInverseThreeClock,
)
from number_compiler.arithmetic.fields.inverse_three_clock import (
    _root_digit_mod64,
)
from number_compiler.arithmetic.fields.morphism_core import DyadicAffineCocycle
from number_compiler.arithmetic.fields.two_adic import v2_nonzero
from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselCylinder,
)

InverseThreeClock = _SharedInverseThreeClock


@dataclass(frozen=True, slots=True)
class ClockedTangentSkeleton:
    """One of seven reusable match/mismatch consumer actions."""

    match: bool
    valuation_bits: int

    def __post_init__(self) -> None:
        if type(self.match) is not bool or type(self.valuation_bits) is not int:
            raise TypeError("tangent skeleton fields require exact types")
        if self.match:
            if self.valuation_bits != 6:
                raise ValueError("a radix-64 match consumes exactly six bits")
        elif not 0 <= self.valuation_bits < 6:
            raise ValueError("a radix-64 mismatch depth lies in 0..5")

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-clocked-tangent", self.match, self.valuation_bits)


@dataclass(frozen=True, slots=True)
class ClockedTangentOccurrence:
    """Reusable skeleton plus exact spatial odd discrepancy payload."""

    skeleton: ClockedTangentSkeleton
    odd_payload: int | None

    def __post_init__(self) -> None:
        if type(self.skeleton) is not ClockedTangentSkeleton:
            raise TypeError("tangent occurrence requires a skeleton")
        if self.skeleton.match:
            if self.odd_payload is not None:
                raise ValueError("matching action has no discrepancy payload")
        elif type(self.odd_payload) is not int or not (self.odd_payload & 1):
            raise ValueError("mismatch payload must be an exact odd integer")

    def apply_higher(self, higher: int) -> int:
        """Apply ``(d-r+64*Z)/2**e`` to the surviving spatial suffix."""
        if type(higher) is not int:
            raise TypeError("higher tangent displacement must be an exact integer")
        if self.skeleton.match:
            return higher
        if self.odd_payload is None:
            raise AssertionError("mismatch occurrence lost its odd payload")
        return self.odd_payload + (higher << (6 - self.skeleton.valuation_bits))


@dataclass(frozen=True, slots=True)
class Radix64CylinderViews:
    """Temporary occupancy and curvature views of one source/root comparison."""

    source_digit: int
    root_digit: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int or not 0 <= value < 64
            for value in (self.source_digit, self.root_digit)
        ):
            raise ValueError("radix-64 view digits must lie in 0..63")

    @property
    def occupancy(self) -> tuple[int, ...]:
        """O_0..O_6; every row is ones followed by zeroes."""
        skeleton = self.skeleton
        live_bits = 6 if skeleton.match else skeleton.valuation_bits
        return tuple(int(bits <= live_bits) for bits in range(7))

    @property
    def curvature(self) -> tuple[int, ...]:
        occupancy = self.occupancy
        return tuple(occupancy[j] - occupancy[j + 1] for j in range(6))

    @property
    def skeleton(self) -> ClockedTangentSkeleton:
        difference = self.source_digit - self.root_digit
        if difference == 0:
            return ClockedTangentSkeleton(True, 6)
        return ClockedTangentSkeleton(False, v2_nonzero(difference))

    @property
    def branch_scale(self) -> int:
        return 1 if self.skeleton.match else 1 << (6 - self.skeleton.valuation_bits)


@dataclass(frozen=True, slots=True)
class NormalizedCylinderJet:
    """Nonnegative integral chart ``W+a = 2**k*V``.

    This owner is exact when the normalized value is integral.  A general
    rational or 2-adic ``W`` needs a scalar owner that admits nonintegral
    values; it must not be encoded by this integer innovation field.
    """

    events: int
    valuation: int
    innovation: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.events, self.valuation, self.innovation)
        ):
            raise TypeError("normalized cylinder fields require exact integers")
        if min(self.events, self.valuation, self.innovation) < 0:
            raise ValueError(self)

    @property
    def cocycle(self) -> DyadicAffineCocycle:
        return DyadicAffineCocycle(1, self.innovation, self.valuation)

    @property
    def normalized_hasse_jet(self) -> tuple[int, int]:
        return (0, 1)

    def then(self, after: NormalizedCylinderJet) -> NormalizedCylinderJet:
        composed = self.cocycle.then(after.cocycle)
        return NormalizedCylinderJet(
            self.events + after.events, composed.shift, composed.addend
        )

    def apply_exact(self, value: int) -> int:
        return self.cocycle.apply_exact(value)


class ClockedTangentArena:
    """Tiny interner for the seven reusable consumer action skeletons."""

    def __init__(self) -> None:
        self._skeletons: dict[tuple[bool, int], ClockedTangentSkeleton] = {}
        self.requests = 0
        self.cache_hits = 0

    def intern(self, *, match: bool, valuation_bits: int) -> ClockedTangentSkeleton:
        self.requests += 1
        key = (match, valuation_bits)
        found = self._skeletons.get(key)
        if found is not None:
            self.cache_hits += 1
            return found
        result = ClockedTangentSkeleton(match, valuation_bits)
        self._skeletons[key] = result
        return result

    @property
    def retained_skeletons(self) -> int:
        return len(self._skeletons)

    def compile(
        self, clock: InverseThreeClock, source_digit: int
    ) -> ClockedTangentOccurrence:
        return radix64_clocked_tangent(clock, source_digit, arena=self)


def radix64_clocked_tangent(
    clock: InverseThreeClock,
    source_digit: int,
    *,
    arena: ClockedTangentArena | None = None,
) -> ClockedTangentOccurrence:
    """Compile a comparison; ``clock.phase`` is the forcing phase ``n+1``."""
    if type(clock) is not InverseThreeClock or clock.precision < 6:
        raise ValueError("clocked tangent needs an inverse-three q>=6 clock")
    if type(source_digit) is not int or not 0 <= source_digit < 64:
        raise ValueError("source digit is outside radix 64")
    views = radix64_cylinder_views(clock, source_digit)
    root_digit = views.root_digit
    difference = source_digit - root_digit
    derived = views.skeleton
    if derived.match:
        skeleton = (
            ClockedTangentSkeleton(True, 6)
            if arena is None
            else arena.intern(match=True, valuation_bits=6)
        )
        return ClockedTangentOccurrence(skeleton, None)
    valuation = derived.valuation_bits
    skeleton = (
        ClockedTangentSkeleton(False, valuation)
        if arena is None
        else arena.intern(match=False, valuation_bits=valuation)
    )
    return ClockedTangentOccurrence(skeleton, difference >> valuation)


def radix64_cylinder_views(
    clock: InverseThreeClock, source_digit: int
) -> Radix64CylinderViews:
    if type(clock) is not InverseThreeClock or clock.precision < 6:
        raise ValueError("radix-64 cylinder view needs a q>=6 clock")
    if type(source_digit) is not int or not 0 <= source_digit < 64:
        raise ValueError("source digit is outside radix 64")
    return Radix64CylinderViews(source_digit, _root_digit_mod64(clock.phase))


def inverse_three_root_cylinder(clock: InverseThreeClock) -> HenselCylinder:
    """Project the clock to the existing exact finite cylinder owner."""
    if type(clock) is not InverseThreeClock:
        raise TypeError("root-cylinder projection requires an inverse-three clock")
    return HenselCylinder(clock.precision, clock.root)


__all__ = [
    "ClockedTangentArena",
    "ClockedTangentOccurrence",
    "ClockedTangentSkeleton",
    "InverseThreeClock",
    "NormalizedCylinderJet",
    "Radix64CylinderViews",
    "inverse_three_root_cylinder",
    "radix64_clocked_tangent",
    "radix64_cylinder_views",
]
