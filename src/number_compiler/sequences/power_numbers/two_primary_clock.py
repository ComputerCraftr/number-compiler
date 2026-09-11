"""Prime-conditional two-primary phase occurrences for special-number clocks.

The action coordinate is only the distance to the unique terminal observation.
Its finite machine is owned by :mod:`number_compiler.arithmetic.functions.finite_unary`.
The odd phase remains exact occurrence payload and is truncated as squaring
increases its two-adic depth.  Nothing in this module establishes that a
candidate is prime or that its carrier has the required pure two-primary shape.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from number_compiler.arithmetic.functions.finite_unary import (
    UnaryQuotientMachine,
    unary_target_distance_machine,
)


@dataclass(frozen=True, slots=True)
class TwoPrimarySurvivalDepthView:
    """Canonical remaining-depth view for one supplied local-depth profile.

    ``remaining=0`` is the single dead sink.  Survival and its first two
    forward differences are demanded observations of this value; they are not
    additional identity fields.  The clipped coordinate differences are
    exposed separately because they are not the derivatives of the survival
    readout.
    """

    remaining: int

    def __post_init__(self) -> None:
        remaining = int(self.remaining)
        if remaining < 0:
            raise ValueError(remaining)
        object.__setattr__(self, "remaining", remaining)

    @property
    def survives(self) -> bool:
        return self.remaining > 0

    @property
    def tangent(self) -> int:
        """First forward difference of the Boolean survival readout."""
        return -1 if self.remaining == 1 else 0

    @property
    def curvature(self) -> int:
        """Second forward difference of the Boolean survival readout."""
        if self.remaining == 1:
            return 1
        if self.remaining == 2:
            return -1
        return 0

    @property
    def remaining_delta(self) -> int:
        """First difference of the clipped remaining-depth coordinate."""
        return -1 if self.survives else 0

    @property
    def remaining_curvature(self) -> int:
        """Second difference caused only by clipping at the dead sink."""
        return int(self.remaining == 1)

    @property
    def derived_views(self) -> tuple[bool, int, int]:
        return self.survives, self.tangent, self.curvature

    @property
    def canonical_key(self) -> tuple[str, int | str]:
        return (
            "two-primary-survival-depth",
            self.remaining if self.remaining else "dead",
        )

    def advance(self, steps: int = 1) -> TwoPrimarySurvivalDepthView:
        steps = int(steps)
        if steps < 0:
            raise ValueError(steps)
        return _survival_depth_view(max(0, self.remaining - steps))


@lru_cache(maxsize=128)
def _survival_depth_view(remaining: int) -> TwoPrimarySurvivalDepthView:
    return TwoPrimarySurvivalDepthView(remaining)


DEAD_TWO_PRIMARY_SURVIVAL_DEPTH = _survival_depth_view(0)


def two_primary_survival_depth_from_remaining(
    remaining: int,
) -> TwoPrimarySurvivalDepthView:
    """Canonicalize an already-proved target-distance action coordinate."""
    remaining = int(remaining)
    if remaining < 0:
        raise ValueError(remaining)
    return _survival_depth_view(remaining)


def two_primary_survival_depth_view(
    local_depths: tuple[int, ...], level: int
) -> TwoPrimarySurvivalDepthView:
    """Derive ``r=d+1-L`` from an externally established depth profile.

    This function does not discover or certify the local depths.  Every
    ``level > min(local_depths)`` returns the identical dead-sink object.
    """
    depths = tuple(map(int, local_depths))
    level = int(level)
    if not depths or any(depth < 0 for depth in depths) or level < 0:
        raise ValueError((depths, level))
    minimum = min(depths)
    if level > minimum:
        return DEAD_TWO_PRIMARY_SURVIVAL_DEPTH
    return _survival_depth_view(minimum + 1 - level)


def mersenne_norm_one_multiply(
    first: tuple[int, int], second: tuple[int, int], modulus: int
) -> tuple[int, int]:
    """Multiply ``a+b*sqrt(3)`` pairs in the concrete Lucas circle algebra."""
    modulus = int(modulus)
    if modulus <= 1:
        raise ValueError(modulus)
    a, b = map(int, first)
    c, d = map(int, second)
    return ((a * c + 3 * b * d) % modulus, (a * d + b * c) % modulus)


def mersenne_norm_one_trace(element: tuple[int, int], modulus: int) -> int:
    """Project a quadratic element and its conjugate to their scalar trace."""
    modulus = int(modulus)
    if modulus <= 1:
        raise ValueError(modulus)
    return (2 * int(element[0])) % modulus


def _order_bits(family: str, parameter: int) -> int:
    family, parameter = str(family), int(parameter)
    if family == "fermat":
        if parameter < 2:
            raise ValueError((family, parameter))
        return 1 << parameter
    if family == "mersenne":
        if parameter < 3 or not parameter & 1:
            raise ValueError((family, parameter))
        return parameter
    raise ValueError(family)


def _v2_bounded(value: int, width: int) -> int:
    if value == 0:
        return width
    return min(width, (value & -value).bit_length() - 1)


def _reduce_nonnegative(value: int, bits: int) -> int:
    """Reduce without constructing ``2**bits`` when the payload already fits."""
    if value < 0:
        raise ValueError(value)
    if value.bit_length() <= bits:
        return value
    return value % (1 << bits)


def _canonical_trace_odd(odd: int, bits: int) -> int:
    odd = _reduce_nonnegative(odd, bits)
    if odd.bit_length() < bits:
        return odd
    modulus = 1 << bits
    return min(odd, (-odd) % modulus)


@dataclass(frozen=True, slots=True)
class PrimeTwoPrimaryPhaseOccurrence:
    """Exact normalized phase beside a shared target-distance action.

    Fermat phases are oriented exponents in a cyclic group of order
    ``2**(2**n)``.  ``exceptional_zero`` distinguishes the ring zero from the
    group identity, although both have the same never-target action.

    Mersenne phases are unoriented norm-one-circle exponents: ``e`` and ``-e``
    have the same trace and are canonicalized together.  This is exact for the
    admitted trace occurrence, but not for an oriented quadratic-ring element.
    """

    family: str
    parameter: int
    depth: int
    odd_phase: int
    exceptional_zero: bool = False

    def __post_init__(self) -> None:
        family, parameter = str(self.family), int(self.parameter)
        width = _order_bits(family, parameter)
        depth, odd = int(self.depth), int(self.odd_phase)
        if not 0 <= depth <= width:
            raise ValueError((depth, width))
        if depth == width:
            if odd != 0:
                raise ValueError((depth, odd))
        elif odd <= 0 or not odd & 1 or odd.bit_length() > width - depth:
            raise ValueError((depth, odd, width))
        if self.exceptional_zero and (family != "fermat" or depth != width or odd):
            raise ValueError((family, depth, odd, self.exceptional_zero))
        if family == "mersenne" and depth < width:
            bits = width - depth
            if odd != _canonical_trace_odd(odd, bits):
                raise ValueError(("noncanonical-trace-phase", odd, bits))
        object.__setattr__(self, "family", family)
        object.__setattr__(self, "parameter", parameter)
        object.__setattr__(self, "depth", depth)
        object.__setattr__(self, "odd_phase", odd)
        object.__setattr__(self, "exceptional_zero", bool(self.exceptional_zero))

    @classmethod
    def from_phase(
        cls,
        family: str,
        parameter: int,
        phase: int,
        *,
        exceptional_zero: bool = False,
    ) -> PrimeTwoPrimaryPhaseOccurrence:
        """Normalize one exact cyclic phase without retaining dead high bits."""
        family, parameter = str(family), int(parameter)
        width = _order_bits(family, parameter)
        if exceptional_zero:
            return cls(family, parameter, width, 0, True)
        phase = int(phase)
        if phase < 0 and family == "mersenne":
            phase = -phase
        phase = _reduce_nonnegative(phase, width)
        depth = _v2_bounded(phase, width)
        if depth == width:
            return cls(family, parameter, width, 0)
        bits = width - depth
        odd = _reduce_nonnegative(phase >> depth, bits)
        if family == "mersenne":
            odd = _canonical_trace_odd(odd, bits)
        return cls(family, parameter, depth, odd)

    @property
    def order_bits(self) -> int:
        return _order_bits(self.family, self.parameter)

    @property
    def retained_phase_bits(self) -> int:
        return self.order_bits - self.depth

    @property
    def phase(self) -> int:
        return self.materialize_phase()

    def materialize_phase(self, *, max_bits: int = 65_536) -> int:
        """Materialize the exponent only after an explicit physical bit gate."""
        max_bits = int(max_bits)
        if max_bits <= 0 or self.order_bits > max_bits:
            raise ValueError(
                ("two-primary-phase-materialization-budget", self.order_bits, max_bits)
            )
        return self.odd_phase << self.depth

    @property
    def target_distance(self) -> int | None:
        """Transitions until ``-1`` (Fermat) or trace zero (Mersenne)."""
        if self.exceptional_zero:
            return None
        terminal_depth = self.order_bits - (1 if self.family == "fermat" else 2)
        if self.depth > terminal_depth:
            return None
        return terminal_depth - self.depth

    @property
    def action_state(self) -> int:
        distance = self.target_distance
        return 0 if distance is None else distance + 1

    @property
    def terminal(self) -> bool:
        return self.target_distance == 0

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "prime-two-primary-phase-occurrence",
            self.family,
            self.parameter,
            self.depth,
            self.odd_phase,
            self.exceptional_zero,
        )

    def jump(self, steps: int) -> PrimeTwoPrimaryPhaseOccurrence:
        """Apply ``steps`` squarings directly and discard newly invisible bits."""
        steps = int(steps)
        if steps < 0:
            raise ValueError(steps)
        if self.exceptional_zero or steps == 0:
            return self
        width = self.order_bits
        depth = min(width, self.depth + steps)
        if depth == width:
            return PrimeTwoPrimaryPhaseOccurrence(self.family, self.parameter, width, 0)
        bits = width - depth
        odd = _reduce_nonnegative(self.odd_phase, bits)
        if self.family == "mersenne":
            odd = _canonical_trace_odd(odd, bits)
        return PrimeTwoPrimaryPhaseOccurrence(self.family, self.parameter, depth, odd)


@lru_cache(maxsize=128)
def _cached_prime_two_primary_depth_clock(
    family: str, parameter: int
) -> UnaryQuotientMachine:
    width = _order_bits(family, parameter)
    max_distance = width - (1 if family == "fermat" else 2)
    return unary_target_distance_machine(max_distance)


def bounded_prime_two_primary_depth_clock(
    family: str,
    parameter: int,
    max_classes: int = 65_537,
) -> UnaryQuotientMachine:
    """Return the shared depth action after an explicit bounded allocation gate.

    This is conditional dynamics, not a prime classifier.  The exact occurrence
    remains outside the returned ActionID.
    """
    family, parameter = str(family), int(parameter)
    width = _order_bits(family, parameter)
    max_distance = width - (1 if family == "fermat" else 2)
    classes = max_distance + 2
    if max_classes <= 0 or classes > int(max_classes):
        raise ValueError(("two-primary-depth-clock-budget", classes, max_classes))
    return _cached_prime_two_primary_depth_clock(family, parameter)


def prime_two_primary_depth_clock_cache_info() -> tuple[int, int, int | None, int]:
    """Expose cache accounting without making an allocation budget semantic."""
    info = _cached_prime_two_primary_depth_clock.cache_info()
    return info.hits, info.misses, info.maxsize, info.currsize


__all__ = [
    "DEAD_TWO_PRIMARY_SURVIVAL_DEPTH",
    "PrimeTwoPrimaryPhaseOccurrence",
    "TwoPrimarySurvivalDepthView",
    "bounded_prime_two_primary_depth_clock",
    "mersenne_norm_one_multiply",
    "mersenne_norm_one_trace",
    "prime_two_primary_depth_clock_cache_info",
    "two_primary_survival_depth_from_remaining",
    "two_primary_survival_depth_view",
]
