"""Independent scalar oracle for Mahler odd-event carry/borrow spectra."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from typing import cast

from number_compiler.sequences.antihydra.mahler_border_identity import (
    MahlerOddMotifSignature,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import MahlerOddToOddAction
from tests.support.exact_integer_power import exact_integer_power


def source_for_motif(word: tuple[int, ...], copies: int, *, extra_bits: int = 8) -> int:
    """Build an exact low-cylinder source for an admitted odd motif."""
    motif = MahlerOddMotifSignature(word)
    bits = tuple(
        bit for exponent in motif.exponents for bit in (1, *((0,) * (exponent - 1)))
    )
    action = MahlerOddToOddAction.from_bits(bits)
    modulus = 1 << (action.extent * copies + extra_bits)
    source = (
        action.joint.innovation
        * pow((1 << action.extent) - action.joint.gain, -1, modulus)
        % modulus
    )
    if source <= 0 or source & 1 == 0:
        raise AssertionError("compiled motif cylinder has no positive odd source")
    return source


def literal_antihydra_summary(
    h: int, width: int
) -> tuple[int, int, int, int, int | None]:
    """Independent term-by-term oracle for physical and ledger coordinates."""
    balance = 0
    minimum = 0
    odd_h_steps = 0
    first_failure: int | None = None
    for index in range(width):
        if h & 1:
            balance -= 1
            odd_h_steps += 1
        else:
            balance += 2
        minimum = min(minimum, balance)
        if balance < 0 and first_failure is None:
            first_failure = index
        h += h // 2
    return h, balance, minimum, odd_h_steps, first_failure


def mapping(value: object) -> Mapping[object, object]:
    """Narrow a JSON-like test payload without casting away its runtime shape."""
    if not isinstance(value, Mapping):
        raise TypeError("expected a mapping payload")
    return cast(Mapping[object, object], value)


def literal_q_harmonic_counts(
    events: Iterable[tuple[int, int, int, int]], *, radix: int, places: int
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    """Return scalar carry, borrow and XOR counts by digit place and phase.

    Each event is ``(q_before, q_after, clock_before, exponent)`` from an
    independently advanced source. The explicit modular recurrence is kept
    here once for both fixed and mixed source-word regressions.
    """
    counts: list[list[list[int]]] = [[[0] * 6 for _ in range(places)] for _ in range(3)]
    for event_index, event in enumerate(events):
        before, after, clock, exponent = event
        for place in range(1, places + 1):
            modulus = exact_integer_power(radix, place)
            product: int = pow(3, exponent, modulus) * (before % modulus) % modulus
            summand: int = pow(2, clock + exponent, modulus)
            next_residue: int = (product + summand) % modulus
            if next_residue != after % modulus:
                raise AssertionError("literal odd-event q recurrence is inconsistent")
            carry = int(product + summand >= modulus)
            borrow = int(next_residue < before % modulus)
            counts[0][place - 1][event_index % 6] += carry
            counts[1][place - 1][event_index % 6] += borrow
            counts[2][place - 1][event_index % 6] += carry ^ borrow
    return tuple(tuple(tuple(phase_row) for phase_row in channel) for channel in counts)
