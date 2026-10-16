"""Certified inward temporal phases of the ``3**(2**t)`` source.

This is a *source* transducer, not a free-standing primality oracle.
For each requested low-radix position it retains the exact digit, ordinary
tripling carry ingress/egress and both H5 bitplanes, all selected by the same
source-level phase.  Decimal periods are proved using multiplicative orders;
short output periods are minimized over a complete periodic orbit, not fitted
to a finite trajectory.  Binary positions have a certified 2-adic transient
and a constant eventual suffix.  No observed period is extended beyond its
proved finite-radix depth, and there is no full-middle harmonic assumption.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from math import lcm
from typing import NamedTuple
from weakref import ReferenceType, ref

from number_compiler.arithmetic.carry.tripling_transfer import (
    IDENTITY,
    CarryFn,
    compose_transfer,
    digit_transfer,
)
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.arithmetic.functions.finite_observer import minimize_finite_orbit
from number_compiler.sequences.power_numbers._harmonic_authority import (
    HarmonicIssuer,
    HarmonicSnapshot,
    harmonic_payload,
    harmonic_snapshot_matches,
    new_harmonic_issuer,
    snapshot_harmonic_payload,
)
from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
    MAX_BINARY_WINDOW_PRECISION,
    MAX_DECIMAL_WINDOW_PRECISION,
    _carry_h5,
    _source_radix_prefix,
)

MAX_ENUMERATED_TEMPORAL_PERIOD = 2_500
_MAX_SOURCE_LEVEL_BITS = 4096


def radix_phase_parameters(base: int, places: int) -> tuple[int, int]:
    """Certified (preperiod, eventual period) of a complete low-radix word.

    For decimal k>=2, ord_(10**k)(3) is a divisor of
        2**max(2,k-2)*5**(k-1).
    After t>=max(2,k-2), 2**t has a fixed 2-primary component.
    Its 5-primary component is periodic with exact order 4*5**(k-2),
    using v5(2**4-1)=1.  For k=1 the residue is eventually 1.
    The full binary residue is 1 once t>=max(1,k-2), as
    v2(3**(2**t)-1)=t+2 for t>=1.
    """
    limit = MAX_BINARY_WINDOW_PRECISION if base == 2 else MAX_DECIMAL_WINDOW_PRECISION
    if type(base) is not int or base not in (2, 10):
        raise ValueError("phase bank admits radix 2 or 10 only")
    if type(places) is not int or not 1 <= places <= limit:
        raise ValueError("phase depth must be positive")
    if base == 2:
        return max(1, places - 2), 1
    if base == 10:
        return max(2, places - 2), (1 if places == 1 else 4 * 5 ** (places - 2))
    raise ValueError("phase bank admits radix 2 or 10 only")


def _certified_temporal_signal_periods(
    base: int,
    position: int,
) -> tuple[tuple[str, int], ...] | None:
    """Minimize *whole* proved eventual orbits, not a sampled window.

    Each residue step x -> x*x (mod b**(position+1)) is an exact
    ``t -> t+1`` source advance.  A period above the explicit orbit budget
    remains symbolic and is never reported as an empirically minimized period.
    """
    depth = position + 1
    transient, orbit_period = radix_phase_parameters(base, depth)
    if orbit_period > MAX_ENUMERATED_TEMPORAL_PERIOD:
        return None
    modulus = base**depth
    below = base**position
    word = []
    residue = _source_radix_prefix(transient, base, depth)
    for _ in range(orbit_period):
        digit = residue // below
        carry_in = (3 * (residue % below)) // below
        carry_out = (3 * residue) // modulus
        word.append((digit, carry_in, carry_out))
        residue = residue * residue % modulus
    # Full-orbit closure is an executable cross-check on the order theorem.
    if residue != _source_radix_prefix(transient, base, depth):
        raise ArithmeticError("source temporal orbit failed to close")
    words = {
        "digit": tuple(s[0] for s in word),
        "carry_in": tuple(s[1] for s in word),
        "carry_out": tuple(s[2] for s in word),
        "carry_bit0": tuple(s[2] & 1 for s in word),
        "carry_bit1": tuple((s[2] >> 1) & 1 for s in word),
        "transfer": tuple(digit_transfer(base, s[0]) for s in word),
        "joint": tuple(word),
    }
    successors = tuple((i + 1) % orbit_period for i in range(orbit_period))
    return tuple(
        (
            key,
            minimize_finite_orbit(
                successors, values, max_states=MAX_ENUMERATED_TEMPORAL_PERIOD
            ).class_count,
        )
        for key, values in words.items()
    )


@dataclass(frozen=True, slots=True)
class InwardTemporalPosition:
    """Exact spatial transfer and eventual temporal successor observers."""

    base: int
    position: int
    source_level: int
    digit: int
    carry_in: int
    carry_out: int
    transfer: CarryFn
    low_carry_h5: WalshH5
    high_carry_h5: WalshH5
    preperiod: int
    source_period: int
    source_phase: int | None
    moore_periods: tuple[tuple[str, int], ...] | None

    @property
    def minimal_future_period(self) -> int | None:
        """Period of the joint (digit,carry-in,carry-out) future emission."""
        return None if self.moore_periods is None else dict(self.moore_periods)["joint"]

    @property
    def minimal_future_phase(self) -> int | None:
        period = self.minimal_future_period
        if period is None or self.source_phase is None:
            return None
        return (self.source_level - self.preperiod) % period


@dataclass(frozen=True, slots=True, weakref_slot=True)
class InwardTemporalPhaseBank:
    """Single shared temporal source phase with exact positional carry ports.

    Every row is a projection of the *same* X_t.  A ``source_period`` is an
    eventual suffix statement, not a claim that the unbounded source or its
    leading Sturmian radial clock has that period.
    """

    base: int
    level: int
    depth: int
    source_prefix: int
    carry_vector: tuple[int, ...]
    positions: tuple[InwardTemporalPosition, ...]
    carry_h5: tuple[WalshH5, WalshH5]
    preperiod: int
    source_period: int
    source_phase: int | None
    joint_moore_period: int | None
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    @property
    def producer_verified(self) -> bool:
        if not self._core_verified():
            return False
        seal = self._phase_seal()
        return all(
            harmonic_snapshot_matches(harmonic_payload(position), expected)
            for position, expected in zip(self.positions, seal.position_snapshots)
        )

    def _phase_seal(self) -> _InwardPhaseSeal:
        seal = self._issuer
        if type(seal) is not _InwardPhaseSeal:
            raise ValueError("unissued inward phase bank")
        return seal

    def _core_verified(self) -> bool:
        seal = self._issuer
        return (
            type(seal) is _InwardPhaseSeal
            and seal.issuer is _INWARD_BANK_ISSUER
            and seal.record() is self
            and self.carry_vector is seal.carry_vector
            and self.positions is seal.positions
            and self.carry_h5 is seal.carry_h5
            and harmonic_snapshot_matches(_inward_core(self), seal.core_snapshot)
            and harmonic_snapshot_matches(self.carry_h5, seal.carry_h5_snapshot)
        )

    def _require_core(self) -> _InwardPhaseSeal:
        if not self._core_verified():
            raise ValueError("unissued or changed inward phase bank")
        return self._phase_seal()

    def _require_position(self, index: int, seal: _InwardPhaseSeal) -> None:
        if not harmonic_snapshot_matches(
            harmonic_payload(self.positions[index]), seal.position_snapshots[index]
        ):
            raise ValueError("unissued or changed inward phase bank: selected position")

    def transfer_between(self, start: int, end: int) -> CarryFn:
        """Composition in LSD->MSD order, entirely from authenticated digits."""
        if (
            type(start) is not int
            or type(end) is not int
            or not (0 <= start <= end <= self.depth)
        ):
            raise ValueError("transfer range exceeds phase bank")
        seal = self._require_core()
        action = IDENTITY
        for index in range(start, end):
            self._require_position(index, seal)
            position = self.positions[index]
            action = compose_transfer(action, position.transfer)
        return action

    def exact_ingress_at(self, depth: int) -> int:
        if type(depth) is not int or not 0 <= depth <= self.depth:
            raise ValueError("carry boundary exceeds phase bank")
        self._require_core()
        return 0 if depth == 0 else self.carry_vector[depth - 1]

    def temporal_power(self, steps: int) -> InwardTemporalPhaseBank:
        """Power the *dyadic level* clock at this certified finite radix depth.

        R(t+steps) = R(t)**(2**steps) modulo base**depth.  The target
        is sourced directly from the modular exponent clock (decimal)
        or the 2-adic binomial formula (binary); no sequence of `steps`
        squarings, no scan of the middle, and no Fermat-candidate modulus.
        This morphism is certified ONLY for the low `depth` digits.
        """
        if type(steps) is not int or steps < 0:
            raise ValueError("temporal powering needs a nonnegative integer")
        target_level = self.level + steps
        if target_level.bit_length() > _MAX_SOURCE_LEVEL_BITS:
            raise ValueError("inward bank source level exceeds its bit budget")
        seal = self._require_core()
        for index in range(self.depth):
            self._require_position(index, seal)
        successor = _phase_bank_from_periods(
            self.base,
            target_level,
            self.depth,
            tuple(position.moore_periods for position in self.positions),
        )
        return successor

    @property
    def joint_future_phase(self) -> int | None:
        """Minimal joint phase only after ALL positional transients expire."""
        self._require_core()
        if self.joint_moore_period is None or self.level < self.preperiod:
            return None
        return (self.level - self.preperiod) % self.joint_moore_period

    def partial_signed_fermat_contribution(self, index: int) -> int:
        """Exact low-block fold only, never a terminal Fermat remainder.

        For w=2**index, bit position j contributes with sign (-1)**(j//w)
        to coefficient 2**(j%w).  Modular reduction of this *finite,
        authenticated* prefix is precisely that signed contribution.
        Missing positions have not been assigned zero.
        """
        if self.base != 2 or type(index) is not int or not 1 <= index <= 16:
            raise ValueError(
                "signed Fermat prefix needs a binary source and valid index"
            )
        self._require_core()
        width = 1 << index
        return self.source_prefix % ((1 << width) + 1)


def demand_inward_temporal_phase_bank(
    base: int, level: int, depth: int
) -> InwardTemporalPhaseBank:
    """Authenticate nested digit/carry/H5 constraints without source replay.

    The low prefix is computed once via the source-derived 2-adic unit or
    the modular dyadic exponent. No per-position exponentiation and no
    enumeration of an exponentially long middle word is performed.
    """
    if type(level) is not int or level < 1 or type(depth) is not int or depth < 1:
        raise ValueError("invalid inward bank source level/depth")
    budget = (
        MAX_BINARY_WINDOW_PRECISION
        if base == 2
        else MAX_DECIMAL_WINDOW_PRECISION
        if base == 10
        else 0
    )
    if not 0 < depth <= budget:
        raise ValueError("inward bank precision exceeds the source budget")
    if level.bit_length() > _MAX_SOURCE_LEVEL_BITS:
        raise ValueError("inward bank source level exceeds its bit budget")
    periods = tuple(_certified_temporal_signal_periods(base, i) for i in range(depth))
    return _phase_bank_from_periods(base, level, depth, periods)


def _phase_bank_from_periods(
    base: int,
    level: int,
    depth: int,
    periods: tuple[tuple[tuple[str, int], ...] | None, ...],
) -> InwardTemporalPhaseBank:
    prefix = _source_radix_prefix(level, base, depth)
    quotient = prefix
    carry = 0
    carries = []
    positions = []
    for i in range(depth):
        digit = quotient % base
        quotient //= base
        before = carry
        carry = (3 * digit + carry) // base
        carries.append(carry)
        preperiod, period = radix_phase_parameters(base, i + 1)
        h5lo, h5hi = _carry_h5((carry,), i)
        positions.append(
            InwardTemporalPosition(
                base,
                i,
                level,
                digit,
                before,
                carry,
                digit_transfer(base, digit),
                h5lo,
                h5hi,
                preperiod,
                period,
                (level - preperiod) % period if level >= preperiod else None,
                periods[i],
            )
        )
    preperiod, source_period = radix_phase_parameters(base, depth)
    known_periods = [p.minimal_future_period for p in positions]
    joint_period = (
        lcm(*(p for p in known_periods if p is not None))
        if all(p is not None for p in known_periods)
        else None
    )
    result = InwardTemporalPhaseBank(
        base,
        level,
        depth,
        prefix,
        tuple(carries),
        tuple(positions),
        _carry_h5(tuple(carries), 0),
        preperiod,
        source_period,
        (level - preperiod) % source_period if level >= preperiod else None,
        joint_period,
    )
    _issue_inward_bank(result)
    return result


class _InwardPhaseSeal(NamedTuple):
    issuer: HarmonicIssuer
    record: ReferenceType[object]
    core_snapshot: HarmonicSnapshot
    carry_vector: tuple[int, ...]
    positions: tuple[InwardTemporalPosition, ...]
    carry_h5: tuple[WalshH5, WalshH5]
    carry_h5_snapshot: HarmonicSnapshot
    position_snapshots: tuple[HarmonicSnapshot, ...]


_INWARD_BANK_ISSUER = new_harmonic_issuer(InwardTemporalPhaseBank)


def _inward_core(bank: InwardTemporalPhaseBank) -> tuple[object, ...]:
    return (
        bank.base,
        bank.level,
        bank.depth,
        bank.source_prefix,
        bank.preperiod,
        bank.source_period,
        bank.source_phase,
        bank.joint_moore_period,
    )


def _issue_inward_bank(bank: InwardTemporalPhaseBank) -> None:
    seal = _InwardPhaseSeal(
        _INWARD_BANK_ISSUER,
        ref(bank),
        snapshot_harmonic_payload(_inward_core(bank)),
        bank.carry_vector,
        bank.positions,
        bank.carry_h5,
        snapshot_harmonic_payload(bank.carry_h5),
        tuple(snapshot_harmonic_payload(harmonic_payload(p)) for p in bank.positions),
    )
    object.__setattr__(bank, "_issuer", seal)


__all__ = [
    "MAX_ENUMERATED_TEMPORAL_PERIOD",
    "InwardTemporalPhaseBank",
    "InwardTemporalPosition",
    "demand_inward_temporal_phase_bank",
    "radix_phase_parameters",
]
