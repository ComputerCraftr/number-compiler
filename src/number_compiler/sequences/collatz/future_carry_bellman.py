"""Bounded same-time carry events on an authenticated all-odd source suffix."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.dyadic_unit_phase import (
    MAX_DYADIC_PHASE_PRECISION,
)
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.sequences.collatz.centered_carry_future import (
    CarryEventHits,
    CenteredCarryFuture,
)


@dataclass(frozen=True, slots=True)
class CenteredCarrySignal:
    """The demanded carry events and the corrected end-of-span numerator."""

    hits: CarryEventHits
    numerator_bits: int
    numerator_residue: int


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
    hits, _ = _evaluate_carry_signal(
        source, cuts, horizon, ledger, max_phase_states, include_correction=False
    )
    return hits.homogeneous


def centered_carry_signal(
    source: int,
    cuts: tuple[int, ...],
    *,
    horizon: int,
    ledger: ResourceLedger,
    max_phase_states: int = 4096,
) -> CenteredCarrySignal:
    """Read both carry lanes on one source and the exact low numerator at the end."""
    hits, numerator = _evaluate_carry_signal(
        source, cuts, horizon, ledger, max_phase_states, include_correction=True
    )
    assert numerator is not None
    return CenteredCarrySignal(hits, max(cuts) + 1, numerator)


def _evaluate_carry_signal(
    source: int,
    cuts: tuple[int, ...],
    horizon: int,
    ledger: ResourceLedger,
    max_phase_states: int,
    *,
    include_correction: bool,
) -> tuple[CarryEventHits, int | None]:
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
    if horizon and not source & 1:
        raise ValueError("future carries require a positive odd source")

    precision = max(cuts) + 1
    if horizon == 0 and not include_correction:
        return CarryEventHits(), None

    owner = ledger.register(
        f"collatz-future-carry-{ledger.owner_count}", "temporal_signal_scratch"
    )
    try:
        scratch = LedgerReservation(ledger, owner)
        try:
            # The centered source, its valuation and the phase period are
            # allocated after their conservative bit capacity is reserved.
            scratch.reserve(nodes=(3 * source.bit_length() + precision + 29) // 30)
            if horizon == 0:
                return CarryEventHits(), source % (1 << precision)
            future = CenteredCarryFuture.from_normalized_source(source, precision)
            reserved_bits = 0

            def reserve_bits(bits: int) -> None:
                nonlocal reserved_bits
                if bits > reserved_bits:
                    scratch.reserve(
                        nodes=(bits + 29) // 30 - (reserved_bits + 29) // 30
                    )
                    reserved_bits = bits

            hits = future.first_same_time_even(
                cuts,
                horizon=horizon,
                max_phase_states=max_phase_states,
                reserve_bits=reserve_bits,
                include_correction=include_correction,
            )
            numerator = None
            if include_correction:
                modulus = 1 << precision
                moving_cut = 1 << horizon if horizon < precision else 0
                numerator = (
                    pow(3, horizon, modulus) * (future.centered % modulus) - moving_cut
                ) % modulus
            return hits, numerator
        finally:
            scratch.retire()
    finally:
        ledger.mark_disposed(owner)
