"""Exact cyclic stencil returns for source-authenticated periodic rays."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys

from .stencil_moore import stencil_cell


def checked_translation(
    word: tuple[int, ...], ledger: ResourceLedger | None
) -> tuple[int, int] | None:
    """Check one- and three-step translations on one cyclic primitive word."""
    size = len(word)
    target = word
    for step in range(1, 4):
        target = tuple(
            stencil_cell(target[i - 1], digit, target[(i + 1) % size])
            for i, digit in enumerate(target)
        )
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_RELATIVE_CHECKS,
                size,
            )
        if step == 2:
            continue
        shifts = (0, 1, -1) if step == 1 else range(-3, 4)
        for shift in shifts:
            if all(digit == word[(i + shift) % size] for i, digit in enumerate(target)):
                return step, shift
    return None


def relative_digit(word: tuple[int, ...], index: int, steps: int) -> int:
    """Read one of the first three rows without retaining intermediate rows."""
    size = len(word)
    if steps == 0:
        return word[index % size]
    if steps == 1:
        return stencil_cell(
            word[(index - 1) % size], word[index % size], word[(index + 1) % size]
        )
    if steps == 2:
        return stencil_cell(
            stencil_cell(
                word[(index - 2) % size], word[(index - 1) % size], word[index % size]
            ),
            stencil_cell(
                word[(index - 1) % size], word[index % size], word[(index + 1) % size]
            ),
            stencil_cell(
                word[index % size], word[(index + 1) % size], word[(index + 2) % size]
            ),
        )
    raise ValueError("unsupported relative action phase")
