"""Independent literal reverse/add transition data for family tests."""

from __future__ import annotations

from collections.abc import Iterator

from number_compiler.arithmetic.fields.radix import digits_lsd


def reverse_decimal(value: int) -> int:
    """Independent literal radix-10 reversal for exact recurrence fixtures."""
    if type(value) is not int or value < 0:
        raise ValueError("literal decimal reversal requires a nonnegative integer")
    return int(str(value)[::-1])


def reverse_add_step(value: int) -> int:
    return value + reverse_decimal(value)


def double_reverse_step(value: int) -> int:
    return 2 * reverse_decimal(value)


def iterate_reverse_add(seed: int, steps: int) -> int:
    if type(steps) is not int or steps < 0:
        raise ValueError("literal reverse/add steps must be nonnegative")
    for _ in range(steps):
        seed = reverse_add_step(seed)
    return seed


def _double_reverse_orbit(seed: int, steps: int) -> Iterator[int]:
    if type(steps) is not int or steps < 0:
        raise ValueError("literal double-reverse steps must be nonnegative")
    yield seed
    for _ in range(steps):
        seed = double_reverse_step(seed)
        yield seed


def double_reverse_orbit(seed: int, steps: int) -> tuple[int, ...]:
    """Return the canonical literal source word and every finite successor."""
    return tuple(_double_reverse_orbit(seed, steps))


def iterate_double_reverse(seed: int, steps: int) -> int:
    """Return one finite iterate without retaining the intermediate orbit."""
    last = seed
    for value in _double_reverse_orbit(seed, steps):
        last = value
    return last


def reverse_add_source_data(
    value: int,
) -> tuple[int, list[int], list[int], int, list[int]]:
    """Return source/target pair sums and the exact decimal carry trace."""
    digits = digits_lsd(value, 10)
    width = len(digits)
    source_pairs = [digits[i] + digits[width - 1 - i] for i in range(width)]
    carries = [0]
    for pair_sum in source_pairs:
        carries.append(int(pair_sum + carries[-1] >= 10))
    successor = reverse_add_step(value)
    target_digits = digits_lsd(successor, 10)
    target_pairs = [
        target_digits[i] + target_digits[-i - 1] for i in range(len(target_digits))
    ]
    if len(target_digits) != width + carries[-1]:
        raise AssertionError("literal reverse/add carry disagrees with output width")
    return width, source_pairs, carries, carries[-1], target_pairs


__all__ = [
    "double_reverse_orbit",
    "double_reverse_step",
    "iterate_double_reverse",
    "iterate_reverse_add",
    "reverse_add_source_data",
    "reverse_add_step",
    "reverse_decimal",
]
