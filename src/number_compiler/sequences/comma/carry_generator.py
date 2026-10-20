"""Bounded powered generator for the two lowest comma carry wires.

The finite phase stores only the sector and its CRT coordinates modulo 4 and
25.  Local returns are powered with the fixed-sector cycle displacement in
``arithmetic``; a separate source-bound wrapper checks that the represented
segment stays inside its authenticated decimal sector.
No harmonic or Entry phase is stored here, and this module makes no native
future-branch selection. Its guard applies only to the represented local
segment. Internal snapshots detect ordinary field corruption; neither they nor
the private construction helpers are a security boundary against arbitrary
private calls or Python object-memory APIs.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from .arithmetic import (
    cycle_transfer,
    decimal_sector,
    phase_prefix_displacement_from_transfer,
)

WorkCharge = Callable[[int], None]
BitsCharge = Callable[[int], None]


def charge_carry_work(
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
    work: int,
    *operands: int,
    extra_bits: int = 0,
) -> None:
    if charge_work is not None:
        charge_work(work)
    if charge_bits is not None:
        charge_bits(sum(value.bit_length() for value in operands) + extra_bits)


@dataclass(frozen=True, slots=True)
class C1Phase:
    """One fixed-sector two-digit phase in CRT coordinates.

    ``mod4`` and ``mod25`` are the only low-suffix coordinates retained.
    The decimal suffix is an exact, transient CRT projection.
    """

    sector: int
    mod4: int
    mod25: int

    def __post_init__(self) -> None:
        if (
            type(self.sector) is not int
            or not 1 <= self.sector <= 9
            or type(self.mod4) is not int
            or not 0 <= self.mod4 < 4
            or type(self.mod25) is not int
            or not 0 <= self.mod25 < 25
        ):
            raise ValueError("invalid comma c1 phase")

    @classmethod
    def from_suffix(cls, sector: int, suffix: int) -> C1Phase:
        if (
            type(sector) is not int
            or not 1 <= sector <= 9
            or type(suffix) is not int
            or not 0 <= suffix < 100
        ):
            raise ValueError("comma c1 suffix requires sector 1..9 and suffix 0..99")
        return cls(sector, suffix % 4, suffix % 25)

    @property
    def suffix(self) -> int:
        """Decode the unique low suffix using ``x=(25*q4+76*q25) mod 100``."""
        _validate_phase(self)
        return (25 * self.mod4 + 76 * self.mod25) % 100

    @property
    def tens(self) -> int:
        return self.suffix // 10

    @property
    def ones(self) -> int:
        return self.suffix % 10

    def step(self) -> C1Phase:
        """Apply the exact CRT form of ``x'=(11*x+sector) mod 100``."""
        _validate_phase(self)
        return C1Phase(
            self.sector,
            (3 * self.mod4 + self.sector) % 4,
            (11 * self.mod25 + self.sector) % 25,
        )

    def advance(
        self,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> C1Phase:
        """Return the closed phase at ``steps mod 50`` without step replay."""
        if type(steps) is not int or steps < 0:
            raise ValueError("comma c1 duration must be a nonnegative integer")
        _validate_phase(self)
        charge_carry_work(charge_work, charge_bits, 4, steps, self.mod4, self.mod25)
        residue = steps % 50
        q4 = (self.sector - self.mod4) % 4 if residue % 2 else self.mod4
        q25 = _advance_mod25(self.mod25, self.sector, residue % 25)
        return C1Phase(self.sector, q4, q25)

    @property
    def c0(self) -> bool:
        """Carry from the ones digit on the next local transition."""
        return self.ones + self.sector >= 10

    @property
    def c1(self) -> bool:
        """Carry from the tens digit on the next local transition."""
        return self.tens + self.ones + int(self.c0) >= 10


def _validate_phase(phase: C1Phase) -> None:
    if type(phase) is not C1Phase:
        raise TypeError("comma c1 operation requires a C1Phase")
    if (
        type(phase.sector) is not int
        or not 1 <= phase.sector <= 9
        or type(phase.mod4) is not int
        or not 0 <= phase.mod4 < 4
        or type(phase.mod25) is not int
        or not 0 <= phase.mod25 < 25
    ):
        raise ValueError("invalid or forged comma c1 phase")


def _phase_signature(phase: C1Phase) -> tuple[int, int, int]:
    _validate_phase(phase)
    return phase.sector, phase.mod4, phase.mod25


_RETURN_SEAL = object()
_BOUND_RETURN_SEAL = object()


def _return_signature(
    start: C1Phase, target: C1Phase, steps: int, count: int
) -> tuple[int, ...]:
    if type(steps) is not int or steps < 0 or type(count) is not int or count < 0:
        raise ValueError("invalid or forged comma c1 return counters")
    return (*_phase_signature(start), *_phase_signature(target), steps, count)


def _initialize_return(
    result: C1Return,
    start: C1Phase,
    target: C1Phase,
    steps: int,
    count: int,
) -> None:
    """Store a return already proved by construction or valid composition.

    The caller supplies a count derived by the exact displacement constructor
    or by summing chronologically adjacent validated returns.
    """
    witness = _return_signature(start, target, steps, count)
    object.__setattr__(result, "_start", start)
    object.__setattr__(result, "_target", target)
    object.__setattr__(result, "_steps", steps)
    object.__setattr__(result, "_count", count)
    object.__setattr__(result, "_witness", witness)
    object.__setattr__(result, "_seal", _RETURN_SEAL)


def _advance_mod25(value: int, sector: int, exponent: int) -> int:
    """Closed affine orbit modulo 25 for exponent ``0..24``."""
    return (
        (1 + 10 * exponent) * value
        + sector * (exponent + 5 * exponent * (exponent - 1))
    ) % 25


def _fixed_sector_displacement(
    phase: C1Phase,
    steps: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    """Apply the sparse weighted C1 power after conservative charging.

    The 100-state weighted matrix has one successor in every row. Its power
    is therefore represented by complete unit-digit cycles plus a tail of
    fewer than ten transitions; the separate CRT phase advance supplies the
    exact suffix endpoint. C1Return derives the accumulated exponent from
    displacement and both suffixes, retaining the physical carry
    ``(x + 10 * (x % 10) + f) // 100``.
    """
    entering_digit = phase.ones
    transfer = cycle_transfer(phase.sector, entering_digit)
    charge_carry_work(
        charge_work,
        charge_bits,
        12 + transfer.period,
        steps,
        phase.suffix,
        extra_bits=4 * steps.bit_length() + 160,
    )
    return phase_prefix_displacement_from_transfer(transfer, steps)


@dataclass(frozen=True, slots=True, init=False)
class C1Return:
    """An immutable powered return whose endpoint and count are derived.

    Construct with ``C1Return(start, steps)``.  The target and count cannot be
    supplied by callers; chronological composition reuses the completed child
    returns and does not invoke the displacement owner again.
    """

    _start: C1Phase
    _target: C1Phase
    _steps: int
    _count: int
    _witness: tuple[int, ...]
    _seal: object

    def __init__(
        self,
        start: C1Phase,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> None:
        if type(start) is not C1Phase:
            raise TypeError("comma c1 return requires a C1Phase source")
        _validate_phase(start)
        if type(steps) is not int or steps < 0:
            raise ValueError("comma c1 duration must be a nonnegative integer")
        charge_carry_work(
            charge_work,
            charge_bits,
            8,
            steps,
            start.suffix,
            extra_bits=4 * steps.bit_length() + 96,
        )
        target = start.advance(steps, charge_work=charge_work, charge_bits=charge_bits)
        displacement = _fixed_sector_displacement(
            start,
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        charge_carry_work(
            charge_work,
            charge_bits,
            1,
            start.suffix,
            displacement,
            target.suffix,
            extra_bits=2,
        )
        numerator = start.suffix + displacement - target.suffix
        if numerator < 0 or numerator % 100:
            raise ArithmeticError("powered comma c1 displacement has a bad endpoint")
        count = numerator // 100
        charge_carry_work(
            charge_work,
            charge_bits,
            1,
            displacement,
            numerator,
            count,
            steps,
            extra_bits=1,
        )
        _initialize_return(self, start, target, steps, count)

    def validate(self) -> None:
        if getattr(self, "_seal", None) is not _RETURN_SEAL:
            raise ValueError("invalid or uninitialized comma c1 return")
        signature = _return_signature(
            self._start, self._target, self._steps, self._count
        )
        if getattr(self, "_witness", None) != signature:
            raise ValueError("comma c1 return fields disagree with their snapshot")

    def structural_snapshot(self) -> tuple[C1Phase, C1Phase, int, int]:
        """Return validated chronological fields for the bound-return owner."""
        self.validate()
        return self._start, self._target, self._steps, self._count

    @property
    def start(self) -> C1Phase:
        self.validate()
        return self._start

    @property
    def target(self) -> C1Phase:
        self.validate()
        return self._target

    @property
    def steps(self) -> int:
        self.validate()
        return self._steps

    @property
    def count(self) -> int:
        self.validate()
        return self._count

    def displacement(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Recover total fixed-sector displacement from the exact return."""
        self.validate()
        charge_carry_work(
            charge_work,
            charge_bits,
            1,
            self._count,
            self._start.suffix,
            self._target.suffix,
            extra_bits=self._count.bit_length() + 8,
        )
        return 100 * self._count + self._target.suffix - self._start.suffix

    def then(
        self,
        after: C1Return,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> C1Return:
        """Compose chronological returns after checking their shared phase."""
        if type(after) is not C1Return:
            raise ValueError("comma c1 returns have different chronological endpoints")
        self.validate()
        after.validate()
        if self._target != after._start:
            raise ValueError("comma c1 returns have different chronological endpoints")
        charge_carry_work(
            charge_work,
            charge_bits,
            1,
            self._steps,
            after._steps,
            self._count,
            after._count,
            extra_bits=2,
        )
        steps = self._steps + after._steps
        count = self._count + after._count
        charge_carry_work(charge_work, charge_bits, 1, steps, count)
        # These children were derived at construction.  Composition is the
        # cocycle law, so no cycle displacement is recomputed here.
        return _completed_return(
            self._start,
            after._target,
            steps,
            count,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )


def _completed_return(
    start: C1Phase,
    target: C1Phase,
    steps: int,
    count: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> C1Return:
    """Finish a return with a child-derived count and checked endpoint.

    The count must come from the exact constructor or validated cocycle
    composition. This private helper checks phase advancement but does not
    independently recalculate the count.
    """
    if type(start) is not C1Phase or type(target) is not C1Phase:
        raise TypeError("completed c1 return requires exact phases")
    charge_carry_work(charge_work, charge_bits, 1, steps, count)
    expected_target = start.advance(
        steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    if expected_target != target:
        raise ValueError("completed c1 return target disagrees with its duration")
    result = object.__new__(C1Return)
    _initialize_return(result, start, target, steps, count)
    return result


@dataclass(frozen=True, slots=True, init=False)
class BoundC1Return:
    """A local return authenticated against one physical source value."""

    _source_high: int
    _action: C1Return
    _target_high: int
    _witness: tuple[int, ...]
    _seal: object

    def __init__(self) -> None:
        raise TypeError("construct BoundC1Return with source_bound_return")

    def validate(self) -> None:
        if getattr(self, "_seal", None) is not _BOUND_RETURN_SEAL:
            raise ValueError("invalid or uninitialized source-bound c1 return")
        if (
            type(self._source_high) is not int
            or self._source_high < 0
            or type(self._target_high) is not int
            or self._target_high < 0
            or type(self._action) is not C1Return
        ):
            raise ValueError("invalid source-bound c1 return fields")
        start, target, steps, count = self._action.structural_snapshot()
        signature = (
            self._source_high,
            self._target_high,
            *_return_signature(start, target, steps, count),
        )
        if getattr(self, "_witness", None) != signature:
            raise ValueError("source-bound c1 fields disagree with their snapshot")

    def structural_snapshot(self) -> tuple[int, C1Return, int]:
        """Return validated physical and local-return fields to owner collaborators."""
        self.validate()
        return self._source_high, self._action, self._target_high

    @property
    def source_high(self) -> int:
        self.validate()
        return self._source_high

    @property
    def action(self) -> C1Return:
        self.validate()
        return self._action

    @property
    def target_high(self) -> int:
        self.validate()
        return self._target_high

    @property
    def start(self) -> C1Phase:
        self.validate()
        return self._action.start

    @property
    def target(self) -> C1Phase:
        self.validate()
        return self._action.target

    @property
    def steps(self) -> int:
        self.validate()
        return self._action.steps

    @property
    def count(self) -> int:
        self.validate()
        return self._action.count

    def then(
        self,
        after: BoundC1Return,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> BoundC1Return:
        """Compose only when both the low phase and high prefix are adjacent."""
        if type(after) is not BoundC1Return:
            raise ValueError("source-bound c1 returns are not chronologically adjacent")
        self.validate()
        after.validate()
        self_target = self._action.structural_snapshot()[1]
        after_start = after._action.structural_snapshot()[0]
        if self_target != after_start or self._target_high != after._source_high:
            raise ValueError("source-bound c1 returns are not chronologically adjacent")
        charge_carry_work(
            charge_work,
            charge_bits,
            1,
            self._source_high,
            self._target_high,
            after._source_high,
            after._target_high,
        )
        action = self._action.then(
            after._action,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        return _completed_bound_return(
            self._source_high,
            action,
            after._target_high,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )

    def high_cylinder(
        self,
        precision: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Project the powered target prefix to ``Z / 10**precision``."""
        self.validate()
        return high_prefix_cylinder(
            self._target_high,
            precision,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )

    def carry_wire(
        self,
        wire: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> bool:
        """Read local c0/c1 carry arithmetic at the powered target phase.

        The source-bound guard covers only ``action.steps`` transitions. This
        observation describes the next fixed-sector arithmetic step; it does
        not admit that next Comma child or resolve a seam/fork.
        """
        self.validate()
        return carry_wire(
            self._action.target,
            self._target_high,
            wire,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )


def _completed_bound_return(
    source_high: int,
    action: C1Return,
    target_high: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> BoundC1Return:
    start, target, steps, count = action.structural_snapshot()
    if (
        type(source_high) is not int
        or source_high < 0
        or type(target_high) is not int
        or target_high < 0
    ):
        raise ValueError("invalid source-bound c1 high prefix")
    charge_carry_work(
        charge_work,
        charge_bits,
        1,
        source_high,
        count,
        target_high,
        extra_bits=1,
    )
    if target_high != source_high + count:
        raise ValueError("source-bound c1 high prefix disagrees with its count")
    result = object.__new__(BoundC1Return)
    object.__setattr__(result, "_source_high", source_high)
    object.__setattr__(result, "_action", action)
    object.__setattr__(result, "_target_high", target_high)
    object.__setattr__(
        result,
        "_witness",
        (
            source_high,
            target_high,
            *_return_signature(start, target, steps, count),
        ),
    )
    object.__setattr__(result, "_seal", _BOUND_RETURN_SEAL)
    return result


def source_bound_return(
    source_value: int,
    start: C1Phase,
    steps: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> BoundC1Return:
    """Build a return only when its full segment stays in the source sector.

    The physical recurrence is authenticated for large comma values (three or
    more decimal digits). Positive-duration segments must satisfy the strict
    fixed-sector guard ``headroom > displacement + (sector < 9)``. This is a
    sufficient uniquely admitted interior condition: it deliberately excludes
    some legal seam children, including the 118 to 199 branch beside 200.
    """
    if type(source_value) is not int or source_value <= 0:
        raise ValueError("comma c1 source must be a positive exact integer")
    if type(start) is not C1Phase:
        raise TypeError("comma c1 source requires a C1Phase")
    _validate_phase(start)
    if type(steps) is not int or steps < 0:
        raise ValueError("comma c1 duration must be a nonnegative integer")
    charge_carry_work(
        charge_work,
        charge_bits,
        20 + source_value.bit_length(),
        source_value,
        steps,
        extra_bits=4 * source_value.bit_length() + 128,
    )
    sector = decimal_sector(source_value)
    if sector.exponent < 2:
        raise ValueError(
            "source-bound c1 return requires at least three decimal digits"
        )
    if start.sector != sector.leading or start.suffix != source_value % 100:
        raise ValueError("c1 phase does not match the authenticated source suffix")

    action = C1Return(
        start,
        steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    displacement = action.displacement(
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    charge_carry_work(
        charge_work,
        charge_bits,
        2,
        source_value,
        displacement,
        sector.headroom,
        action.count,
        extra_bits=1,
    )
    if steps and sector.headroom <= displacement + int(sector.leading < 9):
        raise ValueError("powered c1 return crosses its fixed decimal sector")

    source_high = source_value // 100
    charge_carry_work(
        charge_work,
        charge_bits,
        1,
        source_high,
        action.count,
        extra_bits=1,
    )
    target_high = source_high + action.count
    charge_carry_work(
        charge_work, charge_bits, 1, source_high, action.count, target_high
    )
    return _completed_bound_return(
        source_high,
        action,
        target_high,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


def _decimal_power_mod(
    value: int,
    precision: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    """Return ``value mod 10**precision`` after a pre-allocation budget check."""
    charge_carry_work(
        charge_work,
        charge_bits,
        1,
        value,
        precision,
        extra_bits=precision.bit_length(),
    )
    if precision == 0 or value == 0:
        return 0
    # If 10**precision exceeds value, the projection is value and no modulus
    # needs to be allocated.  Since 10**r > 2**(3r), this test is conservative.
    if precision >= (value.bit_length() + 2) // 3:
        return value
    estimated_modulus_bits = 4 * precision + 1
    charge_carry_work(
        charge_work,
        charge_bits,
        8 + 4 * precision,
        value,
        precision,
        extra_bits=estimated_modulus_bits,
    )
    modulus = int(pow(10, precision))
    return value % modulus


def high_prefix_cylinder(
    high_prefix: int,
    precision: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> int:
    """Project a nonnegative high prefix into its requested 10-adic cylinder."""
    if type(high_prefix) is not int or high_prefix < 0:
        raise ValueError("high prefix must be a nonnegative exact integer")
    if type(precision) is not int or precision < 0:
        raise ValueError("cylinder precision must be a nonnegative exact integer")
    charge_carry_work(charge_work, charge_bits, 1, high_prefix, precision)
    return _decimal_power_mod(
        high_prefix,
        precision,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


def apply_high_prefix_cylinder(
    high_prefix: int,
    count: int,
    precision: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> int:
    """Apply the additive c1 cocycle to a finite high-prefix cylinder."""
    if type(high_prefix) is not int or high_prefix < 0:
        raise ValueError("high prefix must be a nonnegative exact integer")
    if type(count) is not int or count < 0:
        raise ValueError("c1 count must be a nonnegative exact integer")
    if type(precision) is not int or precision < 0:
        raise ValueError("cylinder precision must be a nonnegative exact integer")
    charge_carry_work(charge_work, charge_bits, 2, high_prefix, count, precision)
    charge_carry_work(charge_work, charge_bits, 1, high_prefix, count, extra_bits=1)
    target = high_prefix + count
    charge_carry_work(charge_work, charge_bits, 1, high_prefix, count, target)
    return _decimal_power_mod(
        target,
        precision,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


def carry_wire(
    phase: C1Phase,
    high_prefix: int,
    wire: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> bool:
    """Project the outgoing carry at any decimal wire from phase and prefix.

    Wire zero is c0, wire one is c1, and higher wires are the review formula
    ``c1 and (high_prefix + 1) % 10**(wire-1) == 0``. This returns local
    fixed-sector carry arithmetic only. A source-bound return admits its
    represented segment; this next-step observer does not authenticate the
    next Comma child or resolve a seam/fork. Huge wire requests are resolved
    before a decimal modulus is allocated.
    """
    if type(phase) is not C1Phase:
        raise TypeError("carry wire requires a C1Phase")
    _validate_phase(phase)
    if type(high_prefix) is not int or high_prefix < 0:
        raise ValueError("high prefix must be a nonnegative exact integer")
    if type(wire) is not int or wire < 0:
        raise ValueError("carry wire index must be a nonnegative exact integer")
    charge_carry_work(charge_work, charge_bits, 1, high_prefix, wire)
    if wire == 0:
        return phase.c0
    if wire == 1:
        return phase.c1
    if not phase.c1:
        return False
    charge_carry_work(charge_work, charge_bits, 1, high_prefix, extra_bits=1)
    successor_prefix = high_prefix + 1
    charge_carry_work(charge_work, charge_bits, 1, high_prefix, successor_prefix)
    precision = wire - 1
    # 10**precision cannot divide this positive value when its lower bound is
    # already at least the value's bit length; avoid constructing that power.
    if precision >= (successor_prefix.bit_length() + 2) // 3:
        return False
    return (
        _decimal_power_mod(
            successor_prefix,
            precision,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        == 0
    )


__all__ = [
    "BoundC1Return",
    "C1Phase",
    "C1Return",
    "apply_high_prefix_cylinder",
    "carry_wire",
    "high_prefix_cylinder",
    "source_bound_return",
]
