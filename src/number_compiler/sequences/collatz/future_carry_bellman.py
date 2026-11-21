"""Bounded same-time carry events on an authenticated all-odd source suffix."""

from __future__ import annotations

from typing import Literal

from number_compiler.arithmetic.fields.dyadic_unit_phase import (
    MAX_DYADIC_PHASE_PRECISION,
    DyadicUnitPhase,
    dyadic_carry_frontier,
)
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger


def first_simultaneous_even_carries(
    source: int,
    cuts: tuple[int, ...],
    *,
    horizon: int,
    ledger: ResourceLedger,
    max_phase_states: int = 4096,
) -> int | None:
    """Find the first positive normalized tick with all three carry rows even.

    The source is the exact normalized value at an admitted physical seam.
    For each tick, the sampled rows are the carries of the homogeneous
    3**t, 5**t and 15**t actions on source+1. The source must force the
    complete requested all-odd suffix. The returned offset is one-based in
    normalized ticks, each corresponding to two physical Collatz ticks.
    """
    if type(source) is not int or source < 1:
        raise ValueError("future carries require a positive source")
    if (
        type(cuts) is not tuple
        or not cuts
        or any(type(cut) is not int or cut < 0 for cut in cuts)
        or max(cuts) + 1 > MAX_DYADIC_PHASE_PRECISION
    ):
        raise ValueError("future carry cuts exceed the dyadic precision")
    if type(horizon) is not int or horizon < 0:
        raise ValueError("future carry horizon must be nonnegative")
    if type(max_phase_states) is not int or max_phase_states < 1:
        raise ValueError("future carry phase budget must be positive")
    if type(ledger) is not ResourceLedger:
        raise TypeError("future carry query requires its exact resource ledger")
    if horizon == 0:
        return None
    if not source & 1:
        raise ValueError("future carries require a positive odd source")

    owner = ledger.register(
        f"collatz-future-carry-{ledger.owner_count}", "temporal_signal_scratch"
    )
    try:
        with LedgerReservation(ledger, owner) as scratch:
            # The centered source, its valuation and the phase period are
            # allocated after their conservative bit capacity is reserved.
            precision = max(cuts) + 1
            scratch.reserve(nodes=(3 * source.bit_length() + precision + 29) // 30)
            centered = source + 1
            headroom = (centered & -centered).bit_length() - 1
            if horizon > headroom:
                raise ValueError("future carry horizon exceeds certified odd headroom")
            active_precision = max(1, precision - headroom)
            bases: tuple[Literal[3, 5, 15], ...] = (3, 5, 15)
            period = max(
                DyadicUnitPhase.from_exponent(base, 0, active_precision).order
                for base in bases
            )
            samples = min(horizon, period)
            reserved_bits = 0

            def reserve_bits(bits: int) -> None:
                nonlocal reserved_bits
                if bits > reserved_bits:
                    scratch.reserve(
                        nodes=(bits + 29) // 30 - (reserved_bits + 29) // 30
                    )
                    reserved_bits = bits

            # Stop at the first hit; an absent result needs only one phase orbit.
            for tick in range(1, samples + 1):
                if tick > max_phase_states:
                    raise ValueError("future carry phase budget exceeded")
                for base in bases:
                    phase = DyadicUnitPhase.from_exponent(base, tick, precision)
                    row = dyadic_carry_frontier(
                        phase,
                        centered,
                        0,
                        cuts,
                        carry_width=1,
                        reserve_bits=reserve_bits,
                    )
                    if any(cut.carry for cut in row.cuts):
                        break
                else:
                    return tick
            return None
    finally:
        ledger.mark_disposed(owner)
