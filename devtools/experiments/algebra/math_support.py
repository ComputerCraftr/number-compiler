"""Shared integer helpers for research-only probes."""

from __future__ import annotations

from math import isqrt


def ceil_sqrt(value: int) -> int:
    value = int(value)
    if value < 0:
        raise ValueError(value)
    root = isqrt(value)
    return root if root * root == value else root + 1


__all__ = ["ceil_sqrt"]
