"""Independent literal reverse/add transition data for family tests."""

from __future__ import annotations

from number_compiler.arithmetic.fields.radix import digits_lsd


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
    successor = value + int(str(value)[::-1])
    target_digits = digits_lsd(successor, 10)
    target_pairs = [
        target_digits[i] + target_digits[-i - 1] for i in range(len(target_digits))
    ]
    if len(target_digits) != width + carries[-1]:
        raise AssertionError("literal reverse/add carry disagrees with output width")
    return width, source_pairs, carries, carries[-1], target_pairs


__all__ = ["reverse_add_source_data"]
