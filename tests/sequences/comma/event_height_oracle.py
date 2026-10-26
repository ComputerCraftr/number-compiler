"""Independent exact first-event oracle for comma Entry charts.

This arithmetic belongs to regression tests, not the production transition
selector.  The modular height functions never construct ``10**width``.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, lcm

from tests.sequences.comma.padic_event_oracle import (
    canonical_entry_coordinates,
    exact_integer,
    fixed_sector_coordinates,
    is_prime,
    valuation,
)
from tests.support.exact_integer_power import exact_integer_power


def cycle(leading: int, entering_digit: int) -> tuple[int, int]:
    sector, digit = fixed_sector_coordinates(leading, entering_digit)
    length = 10 // gcd(sector, 10)
    displacement = sum(
        10 * ((digit + index * sector) % 10) + sector for index in range(length)
    )
    return length, displacement


def near_germ(leading: int, headroom: int) -> tuple[int, int, int, str]:
    """Find the first Near inspection from its exact bounded guard."""
    sector = exact_integer(leading, "leading")
    remaining = exact_integer(headroom, "headroom")
    if not 1 <= sector <= 9 or not 1 <= remaining <= 540:
        raise ValueError("invalid Near guard coordinates")
    steps = 0
    reserve = int(sector < 9)
    while True:
        digit = (-remaining) % 10
        increment = 10 * digit + sector
        if remaining <= increment + reserve:
            if sector < 9:
                kind = "fork" if remaining == increment + 1 else "sector_cross"
            else:
                kind = "decade_cross" if remaining <= 10 * digit + 1 else "landmine"
            return steps, remaining, digit, kind
        remaining -= increment
        steps += 1
        if steps > 100:
            raise AssertionError("Near headroom exceeded its bounded termination")


@dataclass(frozen=True, slots=True)
class Event:
    sector: int
    offset: int
    width: int
    cycle_length: int
    cycle_displacement: int
    selected_headroom: int
    cycles: int
    near_steps: int
    event_height: int
    terminal_headroom: int
    event_digit: int
    kind: str
    source_integer: int

    @property
    def completed_height(self) -> int:
        """Inspection height plus the final edge only for a crossing Next."""
        return self.event_height + int(self.kind in ("sector_cross", "decade_cross"))

    @property
    def affine_numerator_constant(self) -> int:
        """Signed ``C`` in ``P*T_guard = L*10**width + C``."""
        return self.cycle_displacement * self.near_steps - self.cycle_length * (
            self.offset + self.selected_headroom
        )


def signature(
    leading: int, offset: int, width: int
) -> tuple[int, int, int, int, int, str, int]:
    """Return bounded event/affine data using modular powers only."""
    sector, coordinate, exponent = canonical_entry_coordinates(leading, offset, width)
    cycle_length, displacement = cycle(sector, coordinate % 10)
    extra = int(sector < 9)
    headroom = (
        1
        + extra
        + (pow(10, exponent, displacement) - coordinate - (1 + extra)) % displacement
    )
    near_steps, terminal_headroom, _digit, kind = near_germ(sector, headroom)
    constant = displacement * near_steps - cycle_length * (coordinate + headroom)
    return (
        cycle_length,
        displacement,
        headroom,
        near_steps,
        terminal_headroom,
        kind,
        constant,
    )


def event_control_observation(
    leading: int, offset: int, width: int
) -> tuple[str, int, int, int, int]:
    """Return control/headroom only, deliberately excluding exact weights.

    This is a test comparison projection, not a semantic identifier or proof
    that equal observations imply equivalent unrestricted future behavior.
    """
    _length, _displacement, headroom, near_steps, terminal, kind, _constant = signature(
        leading, offset, width
    )
    return kind, headroom, near_steps, terminal, (-terminal) % 10


def event(leading: int, offset: int, width: int) -> Event:
    """Exact bounded-width oracle; this is the only path that builds 10**width."""
    sector = exact_integer(leading, "leading")
    coordinate = exact_integer(offset, "offset")
    exponent = exact_integer(width, "width")
    cycle_length, displacement, headroom, near_steps, terminal, kind, constant = (
        signature(sector, coordinate, exponent)
    )
    scale = exact_integer_power(10, exponent)
    if (scale - coordinate - headroom) % displacement:
        raise AssertionError("selected headroom did not close a full cycle")
    cycles = (scale - coordinate - headroom) // displacement
    height = cycles * cycle_length + near_steps
    source_integer = (sector + 1) * scale - terminal
    digit = (-terminal) % 10
    if displacement * height != cycle_length * scale + constant:
        raise AssertionError("inspection height lost its signed affine constant")
    if source_integer != (
        sector * scale + coordinate + cycles * displacement + (headroom - terminal)
    ):
        raise AssertionError(
            "terminal source does not match the cycle/near decomposition"
        )

    if kind == "fork":
        if not (sector < 9 and terminal == 91 - 9 * sector and digit == 9 - sector):
            raise AssertionError("fork headroom normal form changed")
    elif kind == "landmine":
        if not (sector == 9 and 1 <= digit <= 8 and terminal == 10 + 9 * digit):
            raise AssertionError("landmine headroom normal form changed")
    elif kind == "decade_cross":
        if not (sector == 9 and terminal <= 10 * digit + 1):
            raise AssertionError("decade crossing guard changed")
    elif kind == "sector_cross":
        if not (sector < 9 and terminal <= 10 * digit + sector):
            raise AssertionError("ordinary sector crossing guard changed")
    else:
        raise AssertionError("unknown Near event kind")

    return Event(
        sector,
        coordinate,
        exponent,
        cycle_length,
        displacement,
        headroom,
        cycles,
        near_steps,
        height,
        terminal,
        digit,
        kind,
        source_integer,
    )


def ordered_children(source: Event) -> tuple[int, ...]:
    """Exact ordered children, for event fixtures only."""
    scale = exact_integer_power(10, source.width)
    sector = source.sector
    digit = source.event_digit
    if source.kind == "fork":
        return ((sector + 1) * scale - 1, (sector + 1) * scale)
    if source.kind == "sector_cross":
        return (
            (sector + 1) * scale + 10 * digit + sector + 1 - source.terminal_headroom,
        )
    if source.kind == "decade_cross":
        return (10 * scale + 10 * digit + 1 - source.terminal_headroom,)
    if source.kind == "landmine":
        return ()
    raise AssertionError("unknown event kind")


def direct_first_event(leading: int, offset: int, width: int) -> tuple[int, int, str]:
    """Literal reference walk, retained only for the width-five grid."""
    sector, coordinate, exponent = canonical_entry_coordinates(leading, offset, width)
    scale = exact_integer_power(10, exponent)
    value = sector * scale + coordinate
    steps = 0
    while True:
        digit = value % 10
        headroom = (sector + 1) * scale - value
        if sector < 9:
            increment = 10 * digit + sector
            if headroom <= increment + 1:
                kind = "fork" if headroom == increment + 1 else "sector_cross"
                return steps, value, kind
            value += increment
        else:
            increment = 10 * digit + 9
            crossing = 10 * digit + 1
            if headroom <= increment:
                kind = "decade_cross" if headroom <= crossing else "landmine"
                return steps, value, kind
            value += increment
        steps += 1
        if steps > 50_000:
            raise AssertionError("width-five sector failed to reach a terminal event")


def order_ten_mod_prime_power(prime: int, exponent: int) -> int:
    """Multiplicative order for an exact prime coprime to ten."""
    base = exact_integer(prime, "prime")
    level = exact_integer(exponent, "exponent")
    if not is_prime(base) or base in (2, 5) or level < 1:
        raise ValueError(
            "order requires an odd prime not dividing ten and a positive level"
        )
    period = next(
        candidate for candidate in range(1, base) if pow(10, candidate, base) == 1
    )
    for power in range(2, level + 1):
        if pow(10, period, exact_integer_power(base, power)) != 1:
            period *= base
        if pow(10, period, exact_integer_power(base, power)) != 1:
            raise AssertionError("prime-power order lift failed")
    return period


def affine_quotient_mod(
    linear: int, divisor: int, constant: int, width: int, prime: int, level: int
) -> int:
    """Return ``(L*10**w+C)/P mod p**k`` without constructing ``10**w``.

    The signed constant is preserved through reduction. Dividing the reduced
    numerator by ``p**v_p(P)`` is exact because the original affine numerator
    is a multiple of ``P``.
    """
    coefficient = exact_integer(linear, "linear")
    denominator = exact_integer(divisor, "divisor")
    signed_constant = exact_integer(constant, "constant")
    exponent = exact_integer(width, "width")
    base = exact_integer(prime, "prime")
    k = exact_integer(level, "level")
    if coefficient <= 0 or denominator <= 0 or exponent < 0:
        raise ValueError("invalid affine quotient coordinates")
    if not is_prime(base) or k < 1:
        raise ValueError("affine quotient requires a prime and positive level")
    divisor_order = valuation(denominator, base)
    prime_part = exact_integer_power(base, divisor_order)
    unit = denominator // prime_part
    modulus = exact_integer_power(base, k)
    lifted_modulus = exact_integer_power(base, k + divisor_order)
    numerator = (
        coefficient * pow(10, exponent, lifted_modulus) + signed_constant
    ) % lifted_modulus
    if numerator % prime_part:
        raise AssertionError("affine numerator is not divisible by p**v_p(P)")
    quotient = numerator // prime_part
    return (quotient * pow(unit, -1, modulus)) % modulus


def height_mod_prime_power(
    leading: int, offset: int, width: int, prime: int, level: int
) -> int:
    """Project inspection height from signed ``P*T=L*10**w+C`` modulo p^k."""
    base = exact_integer(prime, "prime")
    k = exact_integer(level, "level")
    if not is_prime(base) or k < 1:
        raise ValueError("height projection requires a prime and positive level")
    cycle_length, displacement, _h, _near, _terminal, _kind, constant = signature(
        leading, offset, width
    )
    return affine_quotient_mod(cycle_length, displacement, constant, width, base, k)


def completed_height_mod_prime_power(
    leading: int, offset: int, width: int, prime: int, level: int
) -> int:
    kind = signature(leading, offset, width)[5]
    crossing_edge = int(kind in ("sector_cross", "decade_cross"))
    return (
        height_mod_prime_power(leading, offset, width, prime, level) + crossing_edge
    ) % exact_integer_power(
        exact_integer(prime, "prime"), exact_integer(level, "level")
    )


def source_mod_prime_power(
    leading: int, offset: int, width: int, prime: int, level: int
) -> int:
    base = exact_integer(prime, "prime")
    k = exact_integer(level, "level")
    if not is_prime(base) or k < 1:
        raise ValueError("source projection requires a prime and positive level")
    terminal_headroom = signature(leading, offset, width)[4]
    modulus = exact_integer_power(base, k)
    return ((leading + 1) * pow(10, width, modulus) - terminal_headroom) % modulus


def finite_event_periods(
    leading: int, offset: int, prime: int, level: int
) -> tuple[int, int]:
    """Return inspection/completed-height and terminal-source periods in width."""
    base = exact_integer(prime, "prime")
    k = exact_integer(level, "level")
    if not is_prime(base) or base in (2, 5) or k < 1:
        raise ValueError("finite period requires an odd prime not dividing ten")
    displacement = signature(leading, offset, 9)[1]
    displacement_order = valuation(displacement, base)
    height_period = lcm(924, order_ten_mod_prime_power(base, k + displacement_order))
    source_period = lcm(924, order_ten_mod_prime_power(base, k))
    return height_period, source_period
