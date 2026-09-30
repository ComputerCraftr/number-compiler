"""Independent literal decimal child and whole-phase checks."""

from collections.abc import Callable


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
