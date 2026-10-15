"""Deterministic periodic sources shared by reverse/add bank tests."""

from __future__ import annotations

from random import Random


def periodic_reverse_add_source(period: tuple[int, ...], *, seed: int) -> int:
    """Build one symmetric source with the given exact interior pair period."""
    rng = Random(seed)
    half = [rng.randrange(1, 19)]
    half += [rng.randrange(19) for _ in range(95)]
    half += list(period) * 115
    half += [rng.randrange(19) for _ in range(110)]
    low: list[int] = []
    high: list[int] = []
    for index, symbol in enumerate(half):
        lower, upper = max(0, symbol - 9), min(9, symbol)
        if index == 0:
            upper = min(upper, symbol - 1)
        digit = rng.randrange(lower, upper + 1)
        low.append(digit)
        high.append(symbol - digit)
    return int("".join(map(str, high)) + "".join(map(str, reversed(low))))


__all__ = ["periodic_reverse_add_source"]
