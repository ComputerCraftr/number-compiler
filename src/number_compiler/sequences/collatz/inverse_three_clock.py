"""Finite inverse-three clock views and radix-64 tangent skeletons.

At precision ``q`` the normalized coordinate is ``W_n = 3**(-n) x mod
2**q``.  The exact source prefix remains a spatial occurrence input; neither
it nor a finite evaluated ``W`` value enters the reusable clock identity.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import DyadicAffineCocycle
from number_compiler.arithmetic.fields.two_adic import v2_nonzero
from number_compiler.sequences.collatz.hensel_cylinders import (
    MAX_CYLINDER_BITS,
    HenselCylinder,
    three_unit_phase,
)

_ROOT_DIGITS_MOD64 = tuple(
    -pow(three_unit_phase(phase, 6), -1, 64) % 64 for phase in range(16)
)


def _root_digit_mod64(phase: int) -> int:
    return _ROOT_DIGITS_MOD64[phase & 15]


@dataclass(frozen=True, slots=True)
class InverseThreeClock:
    """Canonical temporal phase at one demanded spatial precision."""

    precision: int
    phase: int

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.precision, self.phase)):
            raise TypeError("inverse-three clock fields require exact integers")
        if not 3 <= self.precision <= MAX_CYLINDER_BITS or self.phase < 0:
            raise ValueError(self)
        object.__setattr__(self, "phase", self.phase % self.period)

    @property
    def period(self) -> int:
        return 1 << (self.precision - 2)

    @property
    def unit(self) -> int:
        return three_unit_phase(self.phase, self.precision)

    @property
    def inverse_unit(self) -> int:
        return pow(self.unit, -1, 1 << self.precision)

    @property
    def root(self) -> int:
        """The exact finite root ``-3**(-phase) mod 2**precision``."""
        return (-self.inverse_unit) % (1 << self.precision)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-inverse-three-clock", self.precision, self.phase)

    def normalized_prefix(self, source_prefix: int) -> int:
        """Evaluate W lazily from the caller's demanded exact q-bit prefix."""
        if type(source_prefix) is not int or source_prefix < 0:
            raise ValueError("source prefix must be a nonnegative exact integer")
        mask = (1 << self.precision) - 1
        return ((source_prefix & mask) * self.inverse_unit) & mask

    def recover_prefix(self, normalized: int) -> int:
        if type(normalized) is not int or not 0 <= normalized < 1 << self.precision:
            raise ValueError("normalized prefix is outside clock precision")
        return normalized * self.unit % (1 << self.precision)

    def advance(self, steps: int = 1) -> InverseThreeClock:
        if type(steps) is not int or steps < 0:
            raise ValueError("clock advance must be nonnegative")
        return InverseThreeClock(self.precision, self.phase + steps)

    def lift_phase_digit(self, digit: int) -> InverseThreeClock:
        """Add the next six temporal phase bits while lifting q to q+6."""
        if type(digit) is not int or not 0 <= digit < 64:
            raise ValueError("temporal radix-64 phase digit is outside 0..63")
        if self.precision + 6 > MAX_CYLINDER_BITS:
            raise ValueError("lifted inverse-three precision exceeds its bound")
        return InverseThreeClock(self.precision + 6, self.phase + digit * self.period)

    @property
    def lift_coefficient(self) -> int:
        """Coefficient of the next temporal phase digit in the root lift."""
        if self.precision < 6:
            raise ValueError("radix-64 root lift requires at least six low bits")
        return 35 if self.precision == 6 else 3

    def lifted_root_digit(self, phase_digit: int) -> int:
        """Return the next six root bits without recomputing a wide power."""
        if type(phase_digit) is not int or not 0 <= phase_digit < 64:
            raise ValueError("temporal radix-64 phase digit is outside 0..63")
        base = InverseThreeClock(self.precision + 6, self.phase).root
        base_digit = (base >> self.precision) & 63
        slope = self.lift_coefficient * _root_digit_mod64(self.phase)
        return (base_digit + slope * phase_digit) & 63


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
    "ClockedTangentOccurrence",
    "ClockedTangentArena",
    "ClockedTangentSkeleton",
    "InverseThreeClock",
    "NormalizedCylinderJet",
    "Radix64CylinderViews",
    "inverse_three_root_cylinder",
    "radix64_cylinder_views",
    "radix64_clocked_tangent",
]
