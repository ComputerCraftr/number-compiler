"""Exact decimal comma-child and guarded cyclotomic-sector arithmetic.

The periodic transfer is a statement about one fixed leading-digit sector.
It is never used to decide which child of a fork has an infinite future.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from math import gcd

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


# Static alphabetic locators for the 17 weighted occurrences of nine actions.
# Nodes: (split row, left index, right index); leaves: (-digit, lower, upper).
# Branches retain exact ordered intervals, including digit 9. No query builds
# a trace or classifies the whole boundary graph. Exhaustively checked in tests.
_PORT_LOCATORS: dict[tuple[int, int], tuple[tuple[int, int, int], ...]] = {
    (1, 0): (
        (18, 1, 4),
        (9, 2, 3),
        (-9, 0, 9),
        (-8, 9, 18),
        (31, 5, 8),
        (25, 6, 7),
        (-7, 18, 25),
        (-6, 25, 31),
        (40, 9, 12),
        (36, 10, 11),
        (-5, 31, 36),
        (-4, 36, 40),
        (43, 13, 14),
        (-3, 40, 43),
        (45, 15, 16),
        (-2, 43, 45),
        (-1, 45, 46),
    ),
    (2, 0): (
        (9, 1, 2),
        (-8, 0, 9),
        (15, 3, 4),
        (-6, 9, 15),
        (19, 5, 6),
        (-4, 15, 19),
        (-2, 19, 21),
    ),
    (2, 1): (
        (9, 1, 2),
        (-9, 0, 9),
        (17, 3, 4),
        (-7, 9, 17),
        (22, 5, 6),
        (-5, 17, 22),
        (25, 7, 8),
        (-3, 22, 25),
        (-1, 25, 26),
    ),
    (3, 0): (
        (22, 1, 8),
        (13, 2, 7),
        (8, 3, 4),
        (-7, 0, 8),
        (12, 5, 6),
        (-4, 8, 12),
        (-1, 12, 13),
        (-8, 13, 22),
        (38, 9, 14),
        (29, 10, 13),
        (27, 11, 12),
        (-5, 22, 27),
        (-2, 27, 29),
        (-9, 29, 38),
        (45, 15, 16),
        (-6, 38, 45),
        (-3, 45, 48),
    ),
    (4, 0): (
        (9, 1, 4),
        (7, 2, 3),
        (-6, 0, 7),
        (-2, 7, 9),
        (18, 5, 6),
        (-8, 9, 18),
        (-4, 18, 22),
    ),
    (4, 1): (
        (11, 1, 4),
        (8, 2, 3),
        (-7, 0, 8),
        (-3, 8, 11),
        (20, 5, 6),
        (-9, 11, 20),
        (26, 7, 8),
        (-5, 20, 26),
        (-1, 26, 27),
    ),
    (5, 0): ((-5, 0, 6),),
    (5, 1): ((7, 1, 2), (-6, 0, 7), (-1, 7, 8)),
    (5, 2): ((8, 1, 2), (-7, 0, 8), (-2, 8, 10)),
    (5, 3): ((9, 1, 2), (-8, 0, 9), (-3, 9, 12)),
    (5, 4): ((9, 1, 2), (-9, 0, 9), (-4, 9, 14)),
    (6, 0): (
        (14, 1, 4),
        (5, 2, 3),
        (-4, 0, 5),
        (-8, 5, 14),
        (16, 5, 6),
        (-2, 14, 16),
        (-6, 16, 23),
    ),
    (6, 1): (
        (15, 1, 4),
        (6, 2, 3),
        (-5, 0, 6),
        (-9, 6, 15),
        (19, 5, 6),
        (-3, 15, 19),
        (27, 7, 8),
        (-7, 19, 27),
        (-1, 27, 28),
    ),
    (7, 0): (
        (20, 1, 6),
        (11, 2, 5),
        (4, 3, 4),
        (-3, 0, 4),
        (-6, 4, 11),
        (-9, 11, 20),
        (38, 7, 12),
        (29, 8, 11),
        (23, 9, 10),
        (-2, 20, 23),
        (-5, 23, 29),
        (-8, 29, 38),
        (44, 13, 16),
        (39, 14, 15),
        (-1, 38, 39),
        (-4, 39, 44),
        (-7, 44, 52),
    ),
    (8, 0): (
        (15, 1, 6),
        (8, 2, 5),
        (3, 3, 4),
        (-2, 0, 3),
        (-4, 3, 8),
        (-6, 8, 15),
        (-8, 15, 24),
    ),
    (8, 1): (
        (18, 1, 6),
        (10, 2, 5),
        (4, 3, 4),
        (-3, 0, 4),
        (-5, 4, 10),
        (-7, 10, 18),
        (27, 7, 8),
        (-9, 18, 27),
        (-1, 27, 29),
    ),
    (9, 0): (
        (27, 1, 12),
        (14, 2, 9),
        (5, 3, 6),
        (2, 4, 5),
        (-1, 0, 2),
        (-2, 2, 5),
        (9, 7, 8),
        (-3, 5, 9),
        (-4, 9, 14),
        (20, 10, 11),
        (-5, 14, 20),
        (-6, 20, 27),
        (44, 13, 16),
        (35, 14, 15),
        (-7, 27, 35),
        (-8, 35, 44),
        (-9, 44, 54),
    ),
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
    residue: int,
    *,
    charge_bits: Callable[[int], None] | None = None,
) -> int:
    """Return ``10**p mod displacement`` for ``p >= 5, p % 924 == residue``.

    The 17 admitted displacements share nine coprime kernels. After exponent
    five the 2/5-primary factor vanishes; its exact lift remains occurrence
    data. A shared halfcycle/rotation evaluator selects the core residue.
    This arithmetic identity supplies no infinite-branch admission.
    """
    if (
        type(displacement) is not int
        or type(residue) is not int
        or not 0 <= residue < 924
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
    exponent = (residue - 5) % period
    if charge_bits is not None:
        charge_bits(
            12 * core.bit_length()
            + seed.bit_length()
            + 2 * core.bit_length()
            + primary.bit_length()
            + displacement.bit_length()
            + residue.bit_length()
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
        digit + int(9 - leading <= digit < 9) if extra else digit + 1,
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
    Every constructed port and search comparison is charged. A static
    alphabetic tree selects one port without walking skipped ports.
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
    # Canonical nonzero predecessor of the orbit residue, matching the
    # signed Entry-to-port chart used by the proof owner.
    first_digit = 10 - leading + orbit % divisor
    inverse = pow(leading // divisor, -1, period)
    first_phase = ((first_digit - orbit) // divisor * inverse) % period
    port = punctured_digit_port(
        leading, first_digit, charge_work=charge_work, charge_bits=charge_bits
    )
    if charge_work is not None:
        charge_work(first_phase)
    first_headroom = (
        phase_prefix_displacement(leading, orbit, first_phase)
        + 10 * first_digit
        + leading
        + extra
        - port.point_germ
    )
    if (first_headroom - reduced_headroom) % 10:
        raise ArithmeticError("comma Near port is not on its diagonal")
    row = ((first_headroom - reduced_headroom) // 10) % (transfer.displacement // 10)
    tree = _PORT_LOCATORS[leading, orbit % divisor]
    node = tree[0]
    comparisons = 0
    while node[0] > 0:
        comparisons += 1
        if charge_work is not None:
            charge_work(1)
        if charge_bits is not None:
            charge_bits(row.bit_length() + node[0].bit_length() + 8)
        node = tree[node[1] if row < node[0] else node[2]]
    digit, lower, upper = -node[0], node[1], node[2]
    if not lower <= row < upper:
        raise ArithmeticError("comma weighted locator has an invalid interval")
    row -= lower
    if digit != first_digit:
        port = punctured_digit_port(
            leading,
            digit,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
    if upper - lower != port.dwell:
        raise ArithmeticError("comma weighted locator has an invalid dwell")
    if charge_work is not None:
        charge_work(4)
    terminal_headroom = 10 * port.digit + leading + extra - port.point_germ - 10 * row
    phase_steps = ((port.digit - orbit) // divisor * inverse) % period
    physical_steps = whole_cycles * period + phase_steps
    if charge_work is not None:
        charge_work(4 + phase_steps)
    if charge_bits is not None:
        charge_bits(
            first_headroom.bit_length()
            + row.bit_length()
            + physical_steps.bit_length()
            + terminal_headroom.bit_length()
            + 4 * headroom.bit_length()
            + 32
        )
    if (
        terminal_headroom <= extra
        or terminal_headroom > 10 * port.digit + leading + extra
        or headroom - phase_prefix_displacement(leading, orbit, physical_steps)
        != terminal_headroom
    ):
        raise ArithmeticError("comma weighted port has an inconsistent physical prefix")
    return NearPortReturn(
        physical_steps, terminal_headroom, port.digit, row, whole_cycles, 1, comparisons
    )


def safe_complete_cycles(
    value: int, transfer: CycleTransfer, remaining_steps: int
) -> int:
    """Largest admitted count of entire phase cycles before a sector seam.

    Strict inequality keeps every child in the same sector throughout the
    skipped block, including at a potential fork equality.
    """
    if type(remaining_steps) is not int or remaining_steps < 0:
        raise ValueError("remaining steps must be nonnegative")
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
    sector = decimal_sector(value)
    if sector.leading != transfer.leading or sector.digit != transfer.entering_digit:
        raise ValueError("cycle transfer has another entering cylinder")
    by_target = remaining_steps // transfer.period
    # comma_safe_cycle_count_maximal: c positive copies have guard
    # G + (c-1)*D < H. Solve this once rather than allocating and evaluating
    # a generic prefix-safety action for every receiving sector occurrence.
    if by_target == 0 or sector.headroom <= transfer.maximum_guard:
        return 0
    by_guard = (sector.headroom - 1 - transfer.maximum_guard) // (
        transfer.displacement
    ) + 1
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
    "comma_port_next",
    "comma_port_previous",
    "cycle_power_residue",
    "cycle_residue_period",
    "cycle_transfer",
    "decimal_sector",
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
