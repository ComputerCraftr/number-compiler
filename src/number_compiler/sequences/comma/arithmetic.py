"""Exact decimal comma-child and guarded cyclotomic-sector arithmetic.

The periodic transfer is a statement about one fixed leading-digit sector.
It is never used to decide which child of a fork has an infinite future.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from math import gcd

from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.domain import coarse_entry_coordinate

# The nine coprime kernels are shared. Each admitted physical displacement
# retains its primary lift and exponent-five seed; those occurrence weights
# cannot be identified merely because their cores agree.
_CORE_PERIODS = {1: 1, 3: 1, 7: 6, 11: 2, 13: 6, 21: 6, 23: 22, 27: 3, 29: 28}
_CYCLE_POWER_LIFTS = {
    60: (3, 20, 2),
    80: (1, 80, 0),
    100: (1, 100, 0),
    120: (3, 40, 1),
    140: (7, 20, 2),
    210: (21, 10, 4),
    220: (11, 20, 6),
    230: (23, 10, 18),
    240: (3, 80, 2),
    260: (13, 20, 8),
    270: (27, 10, 10),
    280: (7, 40, 1),
    290: (29, 10, 24),
    460: (23, 20, 9),
    480: (3, 160, 1),
    520: (13, 40, 4),
    540: (27, 20, 5),
}


def _halfcycle(core: int, base: tuple[int, ...], exponent: int) -> int:
    phase = exponent % (2 * len(base))
    value = base[phase % len(base)]
    return value if phase < len(base) else core - value


def recursive_core_residue(core: int, exponent: int) -> int:
    """Exact decimal power on the nine admitted cores, without powering.

    Halfcycles and rotations are shared arithmetic constants, not source
    states. Core 21 uses the mod-7 result and the mod-3 constraint.
    """
    if (
        type(core) is not int
        or core not in _CORE_PERIODS
        or type(exponent) is not int
        or exponent < 0
    ):
        raise ValueError("invalid comma recursive core")
    if core == 1:
        return 0
    if core == 3:
        return 1
    if core in (7, 21):
        value = _halfcycle(7, (1, 3, 2), exponent)
        return value if core == 7 else value + 7 * ((1 - value) % 3)
    if core == 11:
        return 1 + 9 * (exponent % 2)
    if core == 13:
        return _halfcycle(13, (1, 10, 9), exponent)
    if core == 23:
        return _halfcycle(23, (1, 10, 8, 11, 18, 19, 6, 14, 2, 20, 16), exponent)
    if core == 27:
        return 1 + 9 * (exponent % 3)
    return (
        (1, 10, 13, 14, 24, 8, 22)[exponent % 7]
        * (1, 17, 28, 12)[(exponent // 7) % 4]
        % 29
    )


def cycle_power_residue(
    displacement: int,
    residue: int | CyclotomicClock,
    *,
    charge_bits: Callable[[int], None] | None = None,
) -> int:
    """Return ``10**p mod displacement`` for ``p >= 5, p % 924 == residue``.

    The 17 admitted displacements share nine coprime kernels. After exponent
    five the 2/5-primary factor vanishes; its exact lift remains occurrence
    data. A shared halfcycle/rotation evaluator selects the core residue.
    This arithmetic identity supplies no infinite-branch admission.
    """
    if type(displacement) is not int or not (
        type(residue) is CyclotomicClock
        or (type(residue) is int and 0 <= residue < 924)
    ):
        raise ValueError("invalid comma power residue")
    lift = _CYCLE_POWER_LIFTS.get(displacement)
    if lift is None:
        raise ValueError("unsupported comma cycle displacement")
    core, primary, seed = lift
    period = _CORE_PERIODS[core]
    if period == 1:
        # The raw Frobenius clock is fixed here: its exponent-five seed
        # already satisfies 10*nu = nu mod (displacement/10). Avoid powering
        # and phase reduction for every receiving Entry on these channels.
        if charge_bits is not None:
            charge_bits(17 + displacement.bit_length())
        return primary * seed
    exponent = (
        residue.phase(period, shift=-5)
        if isinstance(residue, CyclotomicClock)
        else (residue - 5) % period
    )
    if charge_bits is not None:
        charge_bits(
            12 * core.bit_length()
            + seed.bit_length()
            + 2 * core.bit_length()
            + primary.bit_length()
            + displacement.bit_length()
            + (14 if isinstance(residue, CyclotomicClock) else residue.bit_length())
            + period.bit_length()
            + 3
        )
    # 10**5 = primary * q, so the multiplicative residue law gives this
    # lift directly. No inverse, factor discovery or full-modulus power.
    return primary * (seed * recursive_core_residue(core, exponent) % core)


def cycle_residue_period(displacement: int) -> int:
    """Shared eventual decimal-power period for the admitted displacement."""
    if type(displacement) is not int:
        raise ValueError("invalid comma cycle displacement")
    lift = _CYCLE_POWER_LIFTS.get(displacement)
    if lift is None:
        raise ValueError("unsupported comma cycle displacement")
    return _CORE_PERIODS[lift[0]]


@dataclass(frozen=True, slots=True)
class DecimalSector:
    leading: int
    scale: int
    exponent: int
    boundary: int
    digit: int
    headroom: int


@dataclass(frozen=True, slots=True)
class CycleTransfer:
    leading: int
    entering_digit: int
    period: int
    displacement: int
    maximum_guard: int


@dataclass(frozen=True, slots=True)
class PuncturedDigitPort:
    """Finite diagonal port; its dwell counts +10 rows, not physical ticks."""

    leading: int
    digit: int
    point_germ: int
    dwell: int
    next_digit: int


@dataclass(frozen=True, slots=True)
class NearPortReturn:
    """Exact physical prefix to the next Near seam, with bounded port selection."""

    physical_steps: int
    terminal_headroom: int
    active_digit: int
    occurrence_row: int
    whole_cycles: int
    port_visits: int
    locator_comparisons: int


def _decimal_scale(value: int) -> tuple[int, int]:
    if type(value) is not int or value <= 0:
        raise ValueError("comma value must be a positive integer")
    # A bit-length estimate avoids converting an arbitrarily large integer to
    # a decimal string (and avoids Python's int-to-string digit limit).
    exponent = ((value.bit_length() - 1) * 30103) // 100000
    scale = pow(10, exponent)
    while value < scale:
        scale //= 10
        exponent -= 1
    while value >= scale * 10:
        scale *= 10
        exponent += 1
    return scale, exponent


def leading_digit(value: int) -> int:
    scale, _ = _decimal_scale(value)
    return value // scale


def decimal_sector(value: int) -> DecimalSector:
    scale, exponent = _decimal_scale(value)
    return _decimal_sector_from_scale(value, scale, exponent)


def _decimal_sector_from_scale(value: int, scale: int, exponent: int) -> DecimalSector:
    """Use an already authenticated decimal scale for a monotone sector walk."""
    if (
        type(value) is not int
        or type(scale) is not int
        or type(exponent) is not int
        or scale <= 0
        or exponent < 0
        or not scale <= value < 10 * scale
    ):
        raise ValueError("decimal sector scale does not contain its value")
    leading = value // scale
    boundary = (leading + 1) * scale if leading < 9 else 10 * scale
    return DecimalSector(
        leading, scale, exponent, boundary, value % 10, boundary - value
    )


def _large_sector_children(value: int, sector: DecimalSector) -> tuple[int, ...]:
    """Classify children from the authentic sector of ``value`` for exponent >= 2.

    Callers must obtain ``sector`` from :func:`decimal_sector` for this value.
    This internal primitive avoids nine candidate leading-digit decompositions.
    """
    return tuple(
        value + increment
        for increment in _sector_child_increments(
            sector.leading, sector.digit, sector.headroom
        )
    )


def _sector_child_increments(f: int, d: int, h: int) -> tuple[int, ...]:
    """Complete ordered seam alternatives for an admitted large sector.

    Both literal values and symbolic Near charts consume this classifier.
    The caller supplies the authenticated leading digit, phase and headroom.
    """
    if f < 9:
        low = 10 * d + f
        high = low + 1
        if h > 10 * d + f + 1:
            return (low,)
        if h == 10 * d + f + 1:
            return (low, high)
        return (high,)
    if h > 10 * d + 9:
        return (10 * d + 9,)
    if h <= 10 * d + 1:
        return (10 * d + 1,)
    return ()


def comma_children(value: int) -> tuple[int, ...]:
    """Return the exact children in numerical order.

    Large sectors use the exact tropical seam rule. Only startup values below
    100 need the bounded nine-candidate search.
    """
    sector = decimal_sector(value)
    if sector.exponent >= 2:
        return _large_sector_children(value, sector)
    digit = sector.digit
    children = tuple(
        value + 10 * digit + new_leading
        for new_leading in range(1, 10)
        if leading_digit(value + 10 * digit + new_leading) == new_leading
    )
    return children


def _cycle_displacement(
    leading: int, entering_digit: int, divisor: int, period: int
) -> int:
    residue = entering_digit % divisor
    return (
        10 * (period * residue + divisor * period * (period - 1) // 2)
        + period * leading
    )


def comma_port_dwell(leading: int, digit: int) -> int:
    """Exact zero-inclusive dwell of one physical comma-port transition."""
    if (
        type(leading) is not int
        or not 1 <= leading <= 9
        or type(digit) is not int
        or not 0 <= digit <= 9
    ):
        raise ValueError("invalid comma port dwell")
    return digit + int(leading == 9 or 9 - leading <= digit < 9)


def cycle_transfer(leading: int, entering_digit: int) -> CycleTransfer:
    if type(leading) is not int or not 1 <= leading <= 9:
        raise ValueError("cycle leading digit must be 1 through 9")
    if type(entering_digit) is not int or not 0 <= entering_digit <= 9:
        raise ValueError("cycle phase must be 0 through 9")
    divisor = gcd(leading, 10)
    period = 10 // divisor
    # The phase visits every digit in this residue class exactly once.  Each
    # literal increment is 10*d + leading, so the whole orbit has this sum.
    displacement = _cycle_displacement(leading, entering_digit, divisor, period)
    # At every prefix the strict interior guard is its next displacement
    # plus one for sectors 1..8 and plus zero for sector 9.  Increments are
    # positive; the final prefix therefore has the maximum guard.
    return CycleTransfer(
        leading,
        entering_digit,
        period,
        displacement,
        displacement + int(leading < 9),
    )


def _validate_cycle_transfer_binding(
    transfer: CycleTransfer, leading: int, digit: int
) -> None:
    """Check a reusable transfer against its exact source cylinder."""
    if type(transfer) is not CycleTransfer or any(
        type(field) is not int
        for field in (
            transfer.leading,
            transfer.entering_digit,
            transfer.period,
            transfer.displacement,
            transfer.maximum_guard,
        )
    ):
        raise ValueError("cycle transfer fields require exact integers")
    if not 1 <= transfer.leading <= 9 or not 0 <= transfer.entering_digit <= 9:
        raise ValueError("cycle transfer has an invalid phase")
    divisor = gcd(transfer.leading, 10)
    period = 10 // divisor
    displacement = _cycle_displacement(
        transfer.leading, transfer.entering_digit, divisor, period
    )
    if (
        transfer.period != period
        or transfer.displacement != displacement
        or transfer.maximum_guard != displacement + int(transfer.leading < 9)
    ):
        raise ValueError("cycle transfer does not match its phase arithmetic")
    if leading != transfer.leading or digit != transfer.entering_digit:
        raise ValueError("cycle transfer has another entering cylinder")


def _validate_entry_headroom_input(
    leading: int,
    coordinate: int,
    residue: int | CyclotomicClock,
    exponent_delta: int,
) -> None:
    if (
        not coarse_entry_coordinate(leading, coordinate)
        or type(exponent_delta) is not int
        or exponent_delta < 0
        or not (
            type(residue) is CyclotomicClock
            or (type(residue) is int and 0 <= residue < 924)
        )
    ):
        raise ValueError("invalid comma Entry headroom input")


def entry_headroom_from_transfer(
    leading: int,
    coordinate: int,
    residue: int | CyclotomicClock,
    transfer: CycleTransfer,
    *,
    exponent_delta: int = 0,
    charge_bits: Callable[[int], None] | None = None,
) -> int:
    """Evaluate Entry headroom using a validated, source-bound transfer.

    ``residue`` is the external occurrence clock.  A small integer residue is
    accepted for existing callers; clock-backed callers project only onto the
    admitted cycle's core period.  The transfer must be the exact arithmetic
    action for ``(leading, coordinate % 10)``; its phase is not interchangeable
    with the external clock. Publication callers separately check the
    sector-dependent canonical Entry envelope.
    """
    _validate_entry_headroom_input(leading, coordinate, residue, exponent_delta)
    _validate_cycle_transfer_binding(transfer, leading, coordinate % 10)
    return _entry_headroom_from_validated_transfer(
        leading,
        coordinate,
        residue,
        transfer,
        exponent_delta=exponent_delta,
        charge_bits=charge_bits,
    )


def _entry_headroom_from_validated_transfer(
    leading: int,
    coordinate: int,
    residue: int | CyclotomicClock,
    transfer: CycleTransfer,
    *,
    exponent_delta: int = 0,
    charge_bits: Callable[[int], None] | None = None,
) -> int:
    """Evaluate headroom after an internal producer validated the binding."""
    if charge_bits is not None:
        phase_bits = (
            14 if isinstance(residue, CyclotomicClock) else residue.bit_length()
        )
        charge_bits(
            leading.bit_length()
            + coordinate.bit_length()
            + exponent_delta.bit_length()
            + phase_bits
            + 16
        )
    if isinstance(residue, CyclotomicClock):
        if exponent_delta == 0:
            power = cycle_power_residue(
                transfer.displacement, residue, charge_bits=charge_bits
            )
        else:
            phase = residue.phase(
                cycle_residue_period(transfer.displacement),
                shift=exponent_delta,
            )
            power = cycle_power_residue(
                transfer.displacement, phase, charge_bits=charge_bits
            )
    else:
        phase = (residue + exponent_delta) % 924
        power = cycle_power_residue(
            transfer.displacement, phase, charge_bits=charge_bits
        )
    extra = int(leading < 9)
    headroom = 1 + extra + (power - coordinate - 1 - extra) % transfer.displacement
    if charge_bits is not None:
        charge_bits(
            transfer.period.bit_length()
            + coordinate.bit_length()
            + headroom.bit_length()
        )
    return headroom


def entry_headroom(
    leading: int,
    coordinate: int,
    residue: int | CyclotomicClock,
    *,
    exponent_delta: int = 0,
    charge_bits: Callable[[int], None] | None = None,
) -> tuple[CycleTransfer, int]:
    """Return an Entry transfer and headroom on the coarse arithmetic domain.

    This compatibility entry point constructs the transfer once and delegates
    to the same validated arithmetic core. Callers processing several clock
    phases for one source should retain the transfer and use
    :func:`entry_headroom_from_transfer`, which checks the supplied source
    binding before evaluation.
    """
    _validate_entry_headroom_input(leading, coordinate, residue, exponent_delta)
    transfer = cycle_transfer(leading, coordinate % 10)
    headroom = _entry_headroom_from_validated_transfer(
        leading,
        coordinate,
        residue,
        transfer,
        exponent_delta=exponent_delta,
        charge_bits=charge_bits,
    )
    return transfer, headroom


def phase_prefix_displacement(leading: int, entering_digit: int, steps: int) -> int:
    """Exact displacement along an admitted fixed-sector phase orbit.

    This is ``comma_period_displacement`` in HOL. Admission belongs to the
    enclosing cycle guard; this function neither examines an endpoint nor
    selects a child at a seam. Complete periods use their exact displacement;
    only the incomplete tail of small residue terms is evaluated, independently
    of the decimal scale and requested run length.
    """
    if (
        type(leading) is not int
        or not 1 <= leading <= 9
        or type(entering_digit) is not int
        or not 0 <= entering_digit <= 9
        or type(steps) is not int
        or steps < 0
    ):
        raise ValueError("invalid comma phase prefix")
    divisor = gcd(leading, 10)
    period = 10 // divisor
    complete, tail = divmod(steps, period)
    displacement = (
        complete * _cycle_displacement(leading, entering_digit, divisor, period)
        if complete
        else 0
    )
    return displacement + sum(
        10 * ((entering_digit + index * leading) % 10) + leading
        for index in range(tail)
    )


def punctured_digit_port(
    leading: int,
    digit: int,
    *,
    charge_work: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
) -> PuncturedDigitPort:
    """Construct one of the 81 local diagonal ports from its exact digit.

    The scalar occurrence row is separate. Puncturing removes digit zero
    from the backward phase rotation; no source occurrence is merged here.
    """
    if (
        type(leading) is not int
        or type(digit) is not int
        or not 1 <= leading <= 9
        or not 1 <= digit <= 9
    ):
        raise ValueError("invalid comma punctured digit port")
    if charge_work is not None:
        charge_work(1)
    if charge_bits is not None:
        charge_bits(leading.bit_length() + digit.bit_length() + 16)
    extra = int(leading < 9)
    return PuncturedDigitPort(
        leading,
        digit,
        (digit + leading + extra) % 10,
        comma_port_dwell(leading, digit),
        comma_port_next(leading, digit),
    )


def classify_near_port(
    leading: int,
    headroom: int,
    *,
    charge_work: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
) -> NearPortReturn:
    """Locate a physical Near prefix through the weighted punctured orbit.

    A bounded selection among at most nine finite ports replaces root/row
    scans. Dwell weights select a diagonal occurrence; physical time comes
    from the original forward digit orbit, plus complete phase cycles.
    The caller authenticates headroom against its source chart. Immediate
    boundaries with headroom <= int(leading < 9) are handled by that caller.
    Every constructed port, residual arithmetic operation and comparison is
    charged. Monotone prefix selection constructs only the selected port; no
    stored observer tree or prefix word is needed.
    """
    if (
        type(leading) is not int
        or type(headroom) is not int
        or not 1 <= leading <= 9
        or headroom <= int(leading < 9)
    ):
        raise ValueError("invalid comma Near port source")
    if charge_work is not None:
        charge_work(8)
    if charge_bits is not None:
        charge_bits(8 * headroom.bit_length() + leading.bit_length() + 32)
    extra = int(leading < 9)
    orbit = (-headroom) % 10
    divisor = gcd(leading, 10)
    period = 10 // divisor
    transfer = cycle_transfer(leading, orbit)
    whole_cycles, remainder = divmod(headroom - 1 - extra, transfer.displacement)
    reduced_headroom = 1 + extra + remainder
    # Select the largest physical prefix within the remaining displacement.
    # Complete cycles are already removed; the search has at most ten positions.
    # Retain the displacement at the lower endpoint instead of reevaluating it.
    lower, upper = 0, period
    displacement = 0
    comparisons = 0
    while lower + 1 < upper:
        middle = (lower + upper) // 2
        if charge_work is not None:
            charge_work(middle + 2)
        if charge_bits is not None:
            charge_bits(64 * middle + 32)
        prefix = phase_prefix_displacement(leading, orbit, middle)
        comparisons += 1
        if prefix <= remainder:
            lower, displacement = middle, prefix
        else:
            upper = middle
    active = (orbit + lower * leading) % 10
    port = punctured_digit_port(
        leading, active, charge_work=charge_work, charge_bits=charge_bits
    )
    terminal_headroom = reduced_headroom - displacement
    if not (
        displacement <= remainder < displacement + 10 * active + leading
        and extra < terminal_headroom <= 10 * active + leading + extra
    ):
        raise ArithmeticError("comma selected prefix has an invalid terminal guard")
    row_numerator = 10 * active + leading + extra - port.point_germ - terminal_headroom
    if row_numerator < 0 or row_numerator % 10:
        raise ArithmeticError("comma selected prefix is not on its diagonal")
    row = row_numerator // 10
    if not 0 <= row < port.dwell:
        raise ArithmeticError("comma selected prefix has an invalid dwell")
    if charge_work is not None:
        charge_work(8)
    if charge_bits is not None:
        charge_bits(4 * headroom.bit_length() + 64)
    physical_steps = whole_cycles * period + lower
    # The retained lower-prefix displacement is the proved complete-period
    # decomposition. Check its balance without running the prefix engine again.
    if (
        headroom - (whole_cycles * transfer.displacement + displacement)
        != terminal_headroom
    ):
        raise ArithmeticError("comma selected prefix has an inconsistent balance")
    return NearPortReturn(
        physical_steps, terminal_headroom, active, row, whole_cycles, 1, comparisons
    )


def is_sector9_landmine_headroom(headroom: int) -> bool:
    """Recognize the exact C1 landmine seam in sector nine.

    For a validated sector-nine Near endpoint, write ``B = h - 1``.  The
    terminal condition is exactly ``18 <= B <= 81`` with ``B`` divisible by
    nine.  This is a terminal fast path only; the headroom remains occurrence
    data and is not promoted into the endpoint action identity.
    """
    if type(headroom) is not int:
        return False
    b = headroom - 1
    return 18 <= b <= 81 and b % 9 == 0


def safe_complete_cycles(
    value: int, transfer: CycleTransfer, remaining_steps: int
) -> int:
    """Largest admitted count of entire phase cycles before a sector seam.

    Strict inequality keeps every child in the same sector throughout the
    skipped block, including at a potential fork equality.
    """
    sector = decimal_sector(value)
    return safe_complete_cycles_from_sector(
        sector.leading, sector.digit, sector.headroom, transfer, remaining_steps
    )


def safe_complete_cycles_from_sector(
    leading: int,
    digit: int,
    headroom: int,
    transfer: CycleTransfer,
    remaining_steps: int,
) -> int:
    """Admit full cycles from an already authenticated decimal-sector port.

    Source-image bindings retain these three exact port fields. Reusing them
    avoids recomputing the decimal scale when the scheduler has already
    authenticated the occurrence and its boundary ports.
    """
    if (
        type(leading) is not int
        or type(digit) is not int
        or type(headroom) is not int
        or not 1 <= leading <= 9
        or not 0 <= digit <= 9
        or headroom <= 0
    ):
        raise ValueError("invalid authenticated comma sector port")
    if type(remaining_steps) is not int or remaining_steps < 0:
        raise ValueError("remaining steps must be nonnegative")
    _validate_cycle_transfer_binding(transfer, leading, digit)
    by_target = remaining_steps // transfer.period
    # comma_safe_cycle_count_maximal: c positive copies have guard
    # G + (c-1)*D < H. Solve this once rather than allocating and evaluating
    # a generic prefix-safety action for every receiving sector occurrence.
    if by_target == 0 or headroom <= transfer.maximum_guard:
        return 0
    by_guard = (headroom - 1 - transfer.maximum_guard) // (transfer.displacement) + 1
    return min(by_target, by_guard)


def comma_port_previous(leading: int, digit: int) -> int:
    """Previous decimal digit in the local comma-port cycle."""
    if (
        type(leading) is not int
        or type(digit) is not int
        or not 1 <= leading <= 9
        or not 0 <= digit <= 9
    ):
        raise ValueError("invalid comma port")
    return (digit + 10 - leading) % 10


def comma_port_next(leading: int, digit: int) -> int:
    """Next nonzero port digit, skipping a physical zero once."""
    previous = comma_port_previous(leading, digit)
    if previous == 0:
        previous = comma_port_previous(leading, previous)
    if not 1 <= previous <= 9:
        raise ArithmeticError("comma punctured port escaped the nonzero alphabet")
    return previous


__all__ = [
    "CycleTransfer",
    "DecimalSector",
    "NearPortReturn",
    "PuncturedDigitPort",
    "classify_near_port",
    "comma_children",
    "comma_port_dwell",
    "comma_port_next",
    "comma_port_previous",
    "cycle_power_residue",
    "cycle_residue_period",
    "cycle_transfer",
    "decimal_sector",
    "entry_headroom",
    "entry_headroom_from_transfer",
    "is_sector9_landmine_headroom",
    "leading_digit",
    "phase_prefix_displacement",
    "punctured_digit_port",
    "recursive_core_residue",
    "safe_complete_cycles",
]


def phase_period(leading: int, last_digit: int) -> tuple[int, int]:
    common = gcd(leading, 10)
    period = 10 // common
    residue = last_digit % common
    displacement = (
        10 * (period * residue + common * period * (period - 1) // 2) + period * leading
    )
    return period, displacement
