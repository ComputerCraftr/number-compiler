"""Exact test sources selected by finite normalized parity words."""

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)


def alternating_collatz_source_action(
    normalized_steps: int, high_fiber_bits: int
) -> tuple[DyadicTerminalFieldAction, int]:
    """Return a source whose normalized parity begins ``0, 1, 0, 1, ...``."""
    if (
        type(normalized_steps) is not int
        or normalized_steps <= 0
        or normalized_steps & 1
        or type(high_fiber_bits) is not int
        or high_fiber_bits <= normalized_steps
    ):
        raise ValueError("alternating Collatz fixture requires positive even extent")
    prefixes = [(1, 0)]
    gain, offset = 1, 0
    for index, odd in enumerate((0, 1) * (normalized_steps // 2)):
        if odd:
            gain, offset = 3 * gain, 3 * offset + (1 << index)
        prefixes.append((gain, offset))
    action = DyadicTerminalFieldAction.from_prefixes(tuple(prefixes))
    return action, (1 << high_fiber_bits) + action.source_residue
