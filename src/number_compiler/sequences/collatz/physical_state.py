"""Lightweight bit/carry coordinates for the physical Collatz primitive."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import require_integer


def odd_carry_state(previous: int, carry: int) -> int:
    previous = require_integer(previous, "previous Collatz bit", 0, 1)
    carry = require_integer(carry, "Collatz carry", 0, 1)
    if previous not in (0, 1) or carry not in (0, 1):
        raise ValueError((previous, carry))
    return 2 + (previous << 1) + carry


def odd_carry_parts(state: int) -> tuple[int, int]:
    state = require_integer(state, "Collatz odd state", 2, 5)
    if not 2 <= state <= 5:
        raise ValueError(state)
    value = state - 2
    return (value >> 1) & 1, value & 1
