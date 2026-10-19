"""Shared process-guard test instrumentation."""

from __future__ import annotations

from collections.abc import Callable


def zero_memory_reader() -> tuple[str, Callable[[int], int]]:
    def read(_pid: int) -> int:
        return 0

    return "test", read


__all__ = ["zero_memory_reader"]
