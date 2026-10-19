"""Small literal Collatz traces shared by focused tests and finite audits."""

from __future__ import annotations


def physical_values(seed: int, ticks: int) -> tuple[int, ...]:
    if type(seed) is not int or seed <= 0 or type(ticks) is not int or ticks < 0:
        raise ValueError("finite Collatz trace requires a positive seed and tick count")
    values = [seed]
    current = seed
    for _ in range(ticks):
        current = (3 * current + 1) if current & 1 else current // 2
        values.append(current)
    return tuple(values)


def normalized_trace(seed: int, steps: int) -> tuple[tuple[int, ...], int]:
    if type(seed) is not int or seed <= 0 or type(steps) is not int or steps < 0:
        raise ValueError(
            "normalized Collatz trace requires a positive seed and step count"
        )
    starts: list[int] = []
    current = seed
    for _ in range(steps):
        starts.append(current)
        current = (3 * current + 1) // 2 if current & 1 else current // 2
    return tuple(starts), current
