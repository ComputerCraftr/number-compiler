"""Small shared deterministic helpers used by benchmark probes."""

from __future__ import annotations

import random


def symmetric_word(rng: random.Random, base: int, width: int) -> tuple[int, ...]:
    half = [rng.randrange(base) for _ in range((width + 1) // 2)]
    return tuple(half + half[-1 - (width & 1) :: -1])


__all__ = ["symmetric_word"]
