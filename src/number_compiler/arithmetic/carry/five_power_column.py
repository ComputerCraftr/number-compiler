"""Bounded stationary decimal columns of powers of five."""

from __future__ import annotations

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.periodic_slp import periodic_word
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_on_error


def five_power_column_word(
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    *,
    column: int,
    exponent: int,
    samples: int,
    max_period: int = 65536,
) -> int:
    """Return decimal column digits for consecutive powers starting at exponent.

    The exponent must be at least column + 1, where the decimal suffix has
    entered its stationary 2-adic unit orbit. Output belongs to the arena. Failed construction
    rolls back the unpublished suffix.
    """
    if arena.ledger is not ledger:
        raise ValueError("column arena belongs to another ledger")
    if type(column) is not int or not 0 <= column < 18:
        raise ValueError("column must be between 0 and 17")
    if type(exponent) is not int or exponent < column + 1:
        raise ValueError("five-power column is not in its stationary band")
    if exponent.bit_length() > 4096:
        raise ValueError("five-power exponent exceeds its work budget")
    if type(samples) is not int or samples < 0:
        raise ValueError("sample count must be a nonnegative integer")
    if samples.bit_length() > 4096:
        raise ValueError("sample count exceeds its work budget")
    if type(max_period) is not int or max_period < 1:
        raise ValueError("period budget must be positive")
    width = column + 1
    period = 1 << max(0, width - 2)
    if period > min(max_period, 65536):
        raise ValueError("five-power period exceeds its budget")
    if pow(5, period, 2**width) != 1:
        raise ValueError("five-power period identity failed")
    if not samples:
        return arena.empty_id
    sampled = min(period, samples)
    start = len(arena.nodes)
    with (
        cleanup_on_error(lambda: arena.rollback_unpublished_suffix(start)),
        ledger.reservation(scratch_owner, entries=sampled, nodes=sampled),
    ):
        modulus: int = 10**width
        divisor: int = 10**column
        residue: int = pow(5, exponent, modulus)
        digits: list[int] = []
        for _ in range(sampled):
            digits.append(residue // divisor)
            residue = residue * 5 % modulus
        return periodic_word(arena, digits, samples)
