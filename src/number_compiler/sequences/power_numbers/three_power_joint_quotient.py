"""Source-owned NC14 dyadic-three carry/borrow, CRT, Walsh and pivot packet.

This is a demand-driven observation of the exact unwrapped source
``X_t = 3**(2**t)``.  The source's normalized difference unit
``U_t = (X_t - 1) // 2**(t+2)`` is projected into finite prime-radix rings
without forming the exponential integer.  All children share the same
original source authority; the finite H5 and Walsh masks are *Mealy outputs*,
not a prime-deciding temporal identity.

Even complete knowledge of an accepted finite CRT modulus does not imply
knowledge modulo ``F_n = 2**(2**n)+1``.  This module never claims otherwise.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.integer_congruence import join_congruences
from number_compiler.arithmetic.fields.walsh import WalshH5, walsh64
from number_compiler.sequences.power_numbers.source_matrix import (
    MAX_MULTIRADIX_PLACES,
    MULTIRADIX_BASES,
    FermatMultiradixPort,
    demand_three_power_multiradix_port,
)
from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
    MAX_PIVOT_PRECISION,
    DyadicPivotMoore,
    UnitInnovationWindow,
    fixed_unit_innovation_window,
    moving_unit_innovation_window,
)

LOW_WALSH_WIDTH = 64
MAX_JOINED_BITS = 256
DEFAULT_RADIX_DEMANDS = (
    (2, 16),
    (3, 10),
    (5, 8),
    (7, 6),
    (10, 6),
    (11, 5),
    (13, 5),
    (27, 4),
)


def _checked_level(index: int, level: int) -> None:
    if type(index) is not int or index < 1 or index.bit_length() > 4096:
        raise ValueError(("invalid-Fermat-index", index))
    if type(level) is not int or level < 1 or level.bit_length() > 4096:
        raise ValueError(("invalid-source-level", level))
    # n can be enormous.  Never lower 2**n just to check this bound.
    if index.bit_length() <= 12 and level >= (1 << index):
        raise ValueError(("level-exceeds-Fermat-source", index, level))
    if index.bit_length() > 12 and level.bit_length() <= 4096:
        return


def _join_crt(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    """Exact generalized CRT, including overlapping base-2/base-5/decimal."""
    result = join_congruences(left, right)
    if result is None:
        raise ValueError("different source ports are inconsistent modulo gcd")
    return result


def _two_adic_unit(level: int, bits: int) -> int:
    if bits == 0:
        return 0
    if bits > MAX_PIVOT_PRECISION:
        raise ValueError(("normalized-unit-precision-budget", bits))
    # This is the same bounded, stable 2-adic unit owned by the pivot quotient.
    return fixed_unit_innovation_window(level, bits).current_bits


def _normalized_unit_residue(level: int, modulus: int, source_modulus: int) -> int:
    """Exact (3^(2^t)-1)/2^(t+2) modulo arbitrary bounded radix modulus.

    Division by 2^(t+2) cannot be performed on an even-modulus source residue.
    The 2-adic component is obtained from the normalized unit's own pumped
    recurrence; the odd component uses invertibility.  CRT joins them.
    """
    if type(modulus) is not int or modulus < 2:
        raise ValueError(modulus)
    if type(source_modulus) is not int or not 0 <= source_modulus < modulus:
        raise ValueError("source residue/modulus mismatch")
    twopart = modulus & -modulus
    oddpart = modulus // twopart
    two_bits = twopart.bit_length() - 1
    even_value = _two_adic_unit(level, two_bits)
    if oddpart == 1:
        return even_value
    scale = pow(2, level + 2, oddpart)
    inverse = pow(scale, -1, oddpart)
    odd_value = ((source_modulus - 1) * inverse) % oddpart
    if twopart == 1:
        return odd_value
    return _join_crt((even_value, twopart), (odd_value, oddpart))[0]


def _normalized_unit_matches_source(
    level: int, modulus: int, source_modulus: int, unit: int
) -> bool:
    """Check a supplied unit against the defining 2-adic and odd equations.

    This is deliberately independent of the packet builder.  It makes public
    dataclass replacement unable to forge a plausible range/CRT residue while
    avoiding a second source-residue resolver call.
    """
    twopart = modulus & -modulus
    oddpart = modulus // twopart
    if unit % twopart != _two_adic_unit(level, twopart.bit_length() - 1):
        return False
    if oddpart == 1:
        return True
    scale = pow(2, level + 2, oddpart)
    return (unit * scale - (source_modulus - 1)) % oddpart == 0


def _binary_source_low(level: int, width: int = LOW_WALSH_WIDTH) -> int:
    if level == 0:
        return 3 & ((1 << width) - 1)
    if level + 2 >= width:
        return 1
    bits = width - level - 2
    return 1 + (_two_adic_unit(level, bits) << (level + 2))


@dataclass(frozen=True, slots=True)
class SourceWalsh64:
    """Complete 64-boundary source tapes, with full Walsh and minimal H5."""

    source_bits: int
    tripling_carry_low: int
    tripling_carry_high: int
    innovation_borrow: int
    successive_borrow: int
    innovation_xor: int
    h5: tuple[WalshH5, ...]
    full_walsh: tuple[tuple[int, ...], ...]

    @classmethod
    def at(cls, level: int) -> SourceWalsh64:
        mask64 = (1 << LOW_WALSH_WIDTH) - 1
        # Resolve the authenticated source at the preceding level once, then
        # derive the adjacent levels by the exact squaring recurrence modulo
        # 2^64.  Each small-modulus source row is a power of the previous one;
        # rebuilding all three rows would rescan the same finite source.
        previous = _binary_source_low(level - 1)
        current = previous * previous & mask64
        following = current * current & mask64
        channels = [current, 0, 0, 0, 0, 0]
        # Boundary j corresponds to bit j-1.  Source/innovation residues are
        # all computed from the same exact 64-bit 2-adic field.
        for j in range(1, LOW_WALSH_WIDTH + 1):
            mod = 1 << j
            low = mod - 1
            before = previous & low
            source = current & low
            after = following & low
            tripling = 3 * source // mod
            innovation = (after - source) % mod
            earlier = (source - before) % mod
            borrow = int(after < source)
            successor_borrow = int(innovation < earlier)
            if tripling & 1:
                channels[1] |= 1 << (j - 1)
            if tripling & 2:
                channels[2] |= 1 << (j - 1)
            if borrow:
                channels[3] |= 1 << (j - 1)
            if successor_borrow:
                channels[4] |= 1 << (j - 1)
            if (tripling & 1) ^ successor_borrow:
                channels[5] |= 1 << (j - 1)
            if int(source + innovation >= mod) != borrow:
                raise ArithmeticError("binary innovation carry/borrow duality failed")
        for item in channels:
            if item & ~mask64:
                raise ArithmeticError("Walsh source mask exceeds 64 positions")
        return cls(
            channels[0],
            channels[1],
            channels[2],
            channels[3],
            channels[4],
            channels[5],
            tuple(WalshH5.from_mask(item, 64) for item in channels),
            tuple(walsh64(item) for item in channels),
        )


@dataclass(frozen=True, slots=True)
class SourceRadialOccurrence:
    """Exact symbolic irrational phase geometry (not a computed phase bit)."""

    level: int
    slope: str = "log_6(3)"

    def __post_init__(self) -> None:
        if type(self.level) is not int or self.level < 1:
            raise ValueError(("invalid-radial-source-level", self.level))
        if self.slope != "log_6(3)":
            raise ValueError(
                "radial source phase must use its authenticated base-6 slope"
            )

    def advance(self, steps: int) -> SourceRadialOccurrence:
        if type(steps) is not int or steps < 0:
            raise ValueError(steps)
        return SourceRadialOccurrence(self.level + steps, self.slope)


@dataclass(frozen=True, slots=True)
class ThreePowerJointQuotient:
    """One source-level owner for finite multiradix and harmonic observations.

    ``crt_modulus`` is a finite source modulus, never a substitute for the
    Fermat candidate modulus.  A terminal quotient is not authorized unless
    the CRT result covers that entire modulus (which normal admitted requests
    do not).  Moving XOR windows are external occurrence ports, not ActionIDs.
    """

    index: int
    level: int
    radial: SourceRadialOccurrence
    radix_ports: tuple[FermatMultiradixPort, ...]
    crt_source: int
    crt_unit: int
    crt_modulus: int
    unit_by_radix: tuple[int, ...]
    following_unit_by_radix: tuple[int, ...]
    pivot: DyadicPivotMoore
    moving_unit_xor: UnitInnovationWindow | None
    candidate_modulus_squarings: int = 0
    source_power_evaluations: int = 0
    small_modulus_squarings: int = 0

    def __post_init__(self) -> None:
        _checked_level(self.index, self.level)
        if (
            type(self.radial) is not SourceRadialOccurrence
            or self.radial.level != self.level
        ):
            raise ValueError("joint source/radial clock disagreement")
        if type(self.radix_ports) is not tuple or not self.radix_ports:
            raise ValueError("joint source requires authenticated radix ports")
        if any(
            type(port) is not FermatMultiradixPort
            or port.index != self.index
            or port.level != self.level
            for port in self.radix_ports
        ):
            raise ValueError("joint packet has a foreign radix source")
        if (
            type(self.pivot) is not DyadicPivotMoore
            or self.pivot.level != self.level
            or self.moving_unit_xor is not None
            and (
                type(self.moving_unit_xor) is not UnitInnovationWindow
                or self.moving_unit_xor.level != self.level
            )
        ):
            raise ValueError("pivot demand is not aligned to the source occurrence")
        if (
            type(self.unit_by_radix) is not tuple
            or type(self.following_unit_by_radix) is not tuple
            or len(self.unit_by_radix) != len(self.radix_ports)
            or len(self.following_unit_by_radix) != len(self.radix_ports)
        ):
            raise ValueError("normalized-unit ports are incomplete")
        expected_source = (0, 1)
        expected_unit = (0, 1)
        for port, normalized, next_unit in zip(
            self.radix_ports,
            self.unit_by_radix,
            self.following_unit_by_radix,
            strict=True,
        ):
            if any(
                type(value) is not int or not 0 <= value < port.modulus
                for value in (normalized, next_unit)
            ):
                raise ValueError("normalized units must be canonical radix residues")
            if not _normalized_unit_matches_source(
                self.level, port.modulus, port.source_residue, normalized
            ) or not _normalized_unit_matches_source(
                self.level + 1, port.modulus, port.next_residue, next_unit
            ):
                raise ValueError("normalized unit does not match its source residue")
            recurrence_delta = (
                next_unit
                - normalized
                - pow(2, self.level + 1, port.modulus) * normalized * normalized
            )
            if recurrence_delta % port.modulus:
                raise ValueError("normalized-unit recurrence does not match the source")
            expected_source = _join_crt(
                expected_source, (port.source_residue, port.modulus)
            )
            expected_unit = _join_crt(expected_unit, (normalized, port.modulus))
        if (
            expected_source != (self.crt_source, self.crt_modulus)
            or expected_unit != (self.crt_unit, self.crt_modulus)
            or self.crt_modulus.bit_length() > MAX_JOINED_BITS
        ):
            raise ValueError("source/normalized-unit CRT witness is inconsistent")
        if (
            self.candidate_modulus_squarings != 0
            or self.source_power_evaluations != len(self.radix_ports)
            or self.small_modulus_squarings != 2 * len(self.radix_ports)
        ):
            raise ValueError("invalid source work ledger")

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"

    @property
    def walsh64(self) -> SourceWalsh64:
        """Compute the constant-width harmonic packet only when requested.

        The frozen packet stores no hidden cache: equality and readonly metric
        observations therefore remain independent of property access order.
        """
        return SourceWalsh64.at(self.level)

    @property
    def crt_coverage(self) -> str:
        """Do not confuse the finite CRT precision with Fermat modulus coverage."""
        # If the Fermat number is longer than the CRT modulus, it cannot be
        # contained in this product.  Avoid materializing 2**(2**index).
        if self.index > 12 or (1 << self.index) >= self.crt_modulus.bit_length():
            return "insufficient-finite-CRT-precision"
        candidate_modulus = (1 << (1 << self.index)) + 1
        return (
            "complete-candidate-coverage"
            if self.crt_modulus % candidate_modulus == 0
            else "insufficient-finite-CRT-precision"
        )

    def advance(self, steps: int, *, moving_width: int = 0) -> ThreePowerJointQuotient:
        if type(steps) is not int or steps < 0:
            raise ValueError(steps)
        selected = tuple((port.base, port.places) for port in self.radix_ports)
        return demand_three_power_joint_quotient(
            self.index, self.level + steps, selected, moving_width=moving_width
        )


def demand_three_power_joint_quotient(
    index: int,
    level: int,
    demands: tuple[tuple[int, int], ...] = DEFAULT_RADIX_DEMANDS,
    *,
    moving_width: int = 12,
) -> ThreePowerJointQuotient:
    """Demand the joint packet with exact source/CRT authority and finite cost."""
    _checked_level(index, level)
    if type(demands) is not tuple or not demands or len(demands) > 8:
        raise ValueError("joint radix demands must be a nonempty exact tuple (<=8)")
    if len(set(demands)) != len(demands):
        raise ValueError("duplicate joint radix demand")
    if type(moving_width) is not int or not 0 <= moving_width <= 64:
        raise ValueError(("moving-width-budget", moving_width))
    for base, places in demands:
        if type(base) is not int or base not in MULTIRADIX_BASES:
            raise ValueError(("unsupported-multiradix-base", base))
        if type(places) is not int or not 1 <= places <= MAX_MULTIRADIX_PLACES:
            raise ValueError(("multiradix-place-budget-exceeded", places))
        if base**places > 1_000_000:
            raise ValueError(("digit-modulus-budget-exceeded", base, places))
    ports = tuple(
        demand_three_power_multiradix_port(index, level, b, j) for b, j in demands
    )
    joined_source = (0, 1)
    joined_unit = (0, 1)
    normalized: list[int] = []
    normalized_next: list[int] = []
    for port in ports:
        current = _normalized_unit_residue(level, port.modulus, port.source_residue)
        following = _normalized_unit_residue(level + 1, port.modulus, port.next_residue)
        normalized.append(current)
        normalized_next.append(following)
        joined_source = _join_crt(joined_source, (port.source_residue, port.modulus))
        joined_unit = _join_crt(joined_unit, (current, port.modulus))
        if joined_source[1].bit_length() > MAX_JOINED_BITS:
            raise ValueError("joined CRT work budget exceeded")
        if joined_source[1] != joined_unit[1]:
            raise ArithmeticError("normalized and source CRT moduli differ")
    pivot = DyadicPivotMoore(level)
    if moving_width and level + 1 + moving_width > MAX_PIVOT_PRECISION:
        raise ValueError(
            ("moving-pivot-precision-budget", level, moving_width, MAX_PIVOT_PRECISION)
        )
    moving = (
        moving_unit_innovation_window(level, moving_width) if moving_width else None
    )
    source_work = sum(
        item.factor_trial_candidates for port in ports for item in port.work
    )
    if source_work > 8 * 500:
        raise ArithmeticError("unexpectedly high finite source work")
    return ThreePowerJointQuotient(
        index,
        level,
        SourceRadialOccurrence(level),
        ports,
        joined_source[0],
        joined_unit[0],
        joined_source[1],
        tuple(normalized),
        tuple(normalized_next),
        pivot,
        moving,
        0,
        len(ports),
        2 * len(ports),
    )


__all__ = [
    "DEFAULT_RADIX_DEMANDS",
    "SourceRadialOccurrence",
    "SourceWalsh64",
    "ThreePowerJointQuotient",
    "WalshH5",
    "demand_three_power_joint_quotient",
]
