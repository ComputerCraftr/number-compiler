"""Independent, bounded arithmetic oracle for comma p-adic events.

This module lives with the tests on purpose: p-adic event observations are not
currently part of the production comma API or transition selector.
"""

from __future__ import annotations

from math import gcd, isqrt

from tests.support.exact_integer_power import exact_integer_power


def exact_integer(value: int, name: str) -> int:
    """Shared exact-integer boundary for independent comma test oracles."""
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    return value


def fixed_sector_coordinates(leading: int, entering_digit: int) -> tuple[int, int]:
    """Validate the common coordinates, leaving each cycle formula separate."""
    sector = exact_integer(leading, "leading")
    digit = exact_integer(entering_digit, "entering_digit")
    if not 1 <= sector <= 9 or not 0 <= digit <= 9:
        raise ValueError("invalid fixed-sector coordinates")
    return sector, digit


def canonical_entry_coordinates(
    leading: int, offset: int, width: int
) -> tuple[int, int, int]:
    """Validate exact coordinates for the independent Entry oracle paths."""
    sector = exact_integer(leading, "leading")
    coordinate = exact_integer(offset, "offset")
    exponent = exact_integer(width, "width")
    if not 1 <= sector <= 9 or not 0 <= coordinate <= 89 + sector or exponent < 5:
        raise ValueError("invalid canonical Entry coordinates")
    return sector, coordinate, exponent


def _positive_event_coordinates(value: int, delta: int) -> tuple[int, int]:
    start = exact_integer(value, "value")
    increment = exact_integer(delta, "delta")
    if start <= 0 or increment <= 0:
        raise ValueError("event coordinates must be positive")
    return start, increment


def is_prime(value: int) -> bool:
    """Small deterministic primality check for the bounded oracle only."""
    number = exact_integer(value, "prime")
    if number < 2:
        return False
    return all(number % divisor for divisor in range(2, isqrt(number) + 1))


def primes_through(limit: int) -> tuple[int, ...]:
    bound = exact_integer(limit, "limit")
    if bound < 0:
        raise ValueError("limit must be nonnegative")
    return tuple(number for number in range(2, bound + 1) if is_prime(number))


def _prime(value: int) -> int:
    prime = exact_integer(value, "prime")
    if not is_prime(prime):
        raise ValueError("prime must be prime and at least two")
    return prime


def valuation(value: int, prime: int) -> int:
    number = exact_integer(value, "value")
    base = _prime(prime)
    if number <= 0:
        raise ValueError("valuation requires a positive integer")
    exponent = 0
    while number % base == 0:
        number //= base
        exponent += 1
    return exponent


def event_sign(value: int, delta: int, prime: int) -> int:
    """Sign of ``v_p(value + delta) - v_p(value)`` for positive inputs."""
    start, increment = _positive_event_coordinates(value, delta)
    base = _prime(prime)
    before = valuation(start, base)
    after = valuation(start + increment, base)
    return (after > before) - (after < before)


def residue_event(value: int, delta: int, prime: int) -> int:
    """Return the bounded gain/loss/neutral event from its exact residue."""
    start, increment = _positive_event_coordinates(value, delta)
    base = _prime(prime)
    delta_valuation = valuation(increment, base)
    modulus = exact_integer_power(base, delta_valuation + 1)
    residue = start % modulus
    if residue == (-increment) % modulus:
        return 1
    if residue == 0:
        return -1
    return 0


def fixed_sector_cycle(leading: int, entering_digit: int) -> tuple[int, ...]:
    """Return one last-digit cycle of decimal increments in a fixed sector."""
    sector, digit = fixed_sector_coordinates(leading, entering_digit)
    length = 10 // gcd(sector, 10)
    return tuple(
        10 * ((digit + index * sector) % 10) + sector for index in range(length)
    )


def p_adic_cycle_period(prime: int, delta: int, displacement: int) -> int:
    """Upper period in cycle index for one fixed-sector event channel.

    The returned period is valid only while the source and every increment
    remain inside the same admitted leading-digit sector.
    """
    base = _prime(prime)
    increment = exact_integer(delta, "delta")
    cycle = exact_integer(displacement, "displacement")
    if increment <= 0 or cycle <= 0:
        raise ValueError("increments and cycle displacement must be positive")
    delta_order = valuation(increment, base)
    cycle_order = valuation(cycle, base)
    return exact_integer_power(base, max(0, delta_order + 1 - cycle_order))
