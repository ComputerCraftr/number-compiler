"""Independent reference arithmetic shared by finite transducer probes."""

from __future__ import annotations

from collections.abc import Callable, Sequence


def reference_pair_half(
    parity: int,
    half: Sequence[int],
    base: int,
    carry_fn: Callable[[int, int, int], int],
) -> tuple[int, tuple[int, ...]]:
    """Compute one reverse/add pair step from a half-word and carry oracle."""
    full = tuple(half) + (tuple(half)[-2::-1] if parity else tuple(half)[::-1])
    width = len(full)
    threshold = base - 1
    left = [0] * (width + 1)
    for index, symbol in enumerate(full):
        left[index + 1] = carry_fn(symbol, left[index], threshold)
    right = [0] * (width + 1)
    for index in range(width - 1, -1, -1):
        right[index] = carry_fn(full[index], right[index + 1], threshold)
    growth = left[width]
    if not growth:
        output = [
            2 * full[index]
            + left[index]
            + right[index + 1]
            - base * (left[index + 1] + right[index])
            for index in range(width)
        ]
    else:
        output = [0] * (width + 1)
        output[0] = full[0] + 1 - base * left[1]
        output[width] = output[0]
        for index in range(1, width):
            output[index] = (
                full[index]
                + full[index - 1]
                + left[index]
                + right[index]
                - base * (left[index + 1] + right[index - 1])
            )
    return len(output) & 1, tuple(output[: (len(output) + 1) // 2])
