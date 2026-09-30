"""Small deterministic input generators shared by verification self-checks."""

from __future__ import annotations

import random


def random_half(rng: random.Random, max_length: int) -> list[int]:
    """Draw a nonzero-leading pair half with the historical probe distribution."""
    half = [rng.randrange(19) for _ in range(rng.randrange(1, max_length + 1))]
    half[0] = half[0] or 1
    return half
