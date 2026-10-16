"""Shared monkeypatch helpers for finite dyadic power-number source tests."""

from __future__ import annotations

import pytest


def track_two_adic_source_demands(
    monkeypatch: pytest.MonkeyPatch,
) -> list[tuple[int, int]]:
    """Record exact level/precision calls while preserving source computation."""
    from number_compiler.sequences.power_numbers import (
        three_dyadic_boolean_counter as counter,
    )

    calls: list[tuple[int, int]] = []
    original = counter.two_adic_unit_binomial

    def track(level: int, precision: int) -> int:
        calls.append((level, precision))
        return original(level, precision)

    monkeypatch.setattr(counter, "two_adic_unit_binomial", track)
    return calls


__all__ = ["track_two_adic_source_demands"]
