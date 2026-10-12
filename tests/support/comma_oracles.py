"""Independent literal decimal child and whole-phase checks."""

import math
from collections.abc import Callable

from number_compiler.sequences.comma.arithmetic import decimal_sector


def literal_children(value: int) -> tuple[int, ...]:
    digit = value % 10
    children: list[int] = []
    for child_digit in range(1, 10):
        candidate = value + 10 * digit + child_digit
        if int(str(candidate)[0]) == child_digit:
            children.append(candidate)
    return tuple(children)


def assert_phase_period(period: Callable[[int, int], tuple[int, int]]) -> None:
    for leading in range(1, 10):
        for digit in range(10):
            length, displacement = period(leading, digit)
            current = 10_000 + digit
            original = current
            for _ in range(length):
                current += 10 * (current % 10) + leading
            assert current - original == displacement
            assert current % 10 == original % 10


def literal_phase_jump(value: int) -> tuple[int, int]:
    """Derive an admitted whole phase using only literal child enumeration."""
    sector = decimal_sector(value)
    period = 10 // math.gcd(sector.leading, 10)
    cursor = value
    maximum = 0
    for _ in range(period):
        children = literal_children(cursor)
        if len(children) != 1 or decimal_sector(children[0]).leading != sector.leading:
            return value, 0
        cursor = children[0]
        maximum = max(maximum, cursor - value)
    displacement = cursor - value
    # A second full phase has exactly the same literal offset because the
    # last digit returned to its entering value.  Strict admission is tested
    # at the last visited term of each repeated phase.
    headroom = sector.boundary - value
    count = (headroom - 1 - maximum) // displacement + 1
    if count <= 0:
        return value, 0
    # Being inside the sector does not imply uniqueness: the last edge of
    # the last candidate cycle can be a fork. Check that bounded phase by
    # independent child enumeration, without the production guard formula.
    last_cursor = value + (count - 1) * displacement
    for _ in range(period):
        children = literal_children(last_cursor)
        if len(children) != 1 or decimal_sector(children[0]).leading != sector.leading:
            count -= 1
            break
        last_cursor = children[0]
    return value + count * displacement, count * period
