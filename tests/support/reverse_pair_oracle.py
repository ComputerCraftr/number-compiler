"""Exact scalar reverse-pair oracle shared by independent tests."""

from devtools.verification.oracles.sequence_arithmetic import (
    reference_successor,
)

__all__ = ("reference_successor",)


def symmetric_reference_successor(
    full: tuple[int, ...], base: int = 10
) -> tuple[int, ...]:
    result = reference_successor(full, base)
    assert result == result[::-1]
    return result


def reference_power(
    values: tuple[int, ...], base: int, steps: int
) -> tuple[tuple[int, ...], list[int], list[int]]:
    expected = values
    widths = [len(values)]
    growths: list[int] = []
    for _ in range(steps):
        following = symmetric_reference_successor(expected, base)
        growths.append(len(following) - len(expected))
        widths.append(len(following))
        expected = following
    return expected, growths, widths
