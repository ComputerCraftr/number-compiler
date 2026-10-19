"""Data-only chronological composition for issued reverse/add ring banks."""

from __future__ import annotations

from number_compiler.arithmetic.polynomials.polynomial import f5_modes
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from .macro_conditioned_harmonics import MacroPhaseInwardOrbit
from .temporal_ring_harmonics import (
    ReverseAddTemporalRingBank,
    RingPhaseHarmonic,
    TemporalRingBankPayload,
    finite_future_classes,
    finite_output_period,
)


def compose_temporal_ring_bank_payload(
    first: ReverseAddTemporalRingBank,
    later: ReverseAddTemporalRingBank,
) -> TemporalRingBankPayload:
    """Compose adjacent bank data; authority is checked by the issuer."""
    if (
        first.certificate is not later.certificate
        or first.start + first.duration != later.start
        or first.widths[-1] != later.widths[0]
        or first.positions != later.positions
    ):
        raise ValueError("ring programs require the same issued temporal seam")
    for pos in first.positions:
        if first.target_pair_domain(pos) != later.source_pair_domain(pos):
            raise ValueError("conditional Q19 source/target port seam mismatch")
    center_seam = tuple(
        sorted(set(first.center_domains[-1]) & set(later.center_domains[0]))
    )
    if not center_seam:
        raise ValueError("joint center fiber has no temporal seam")

    def merge_residue(left: int | None, right: int | None) -> int | None:
        if left is not None and right is not None and left != right:
            raise ValueError("joint cyclotomic port has no temporal seam")
        return left if left is not None else right

    combined_centers = (
        first.center_domains[:-1] + (center_seam,) + later.center_domains[1:]
    )
    combined_mod99 = (
        first.global_residues99[:-1]
        + (merge_residue(first.global_residues99[-1], later.global_residues99[0]),)
        + later.global_residues99[1:]
    )
    combined_mod198 = (
        first.global_residues198[:-1]
        + (merge_residue(first.global_residues198[-1], later.global_residues198[0]),)
        + later.global_residues198[1:]
    )
    ledger = first.certificate.owner.ledger
    orbits = tuple(
        MacroPhaseInwardOrbit(
            position,
            left.pair_f5 + right.pair_f5,
            left.low_carries + right.low_carries,
            left.reflected_carries + right.reflected_carries,
            left.reflected_xor + right.reflected_xor,
            left.raw_innovation_borrow + right.raw_innovation_borrow,
            left.carry_borrow_xor + right.carry_borrow_xor,
            left.low_birth + right.low_birth,
            left.low_death + right.low_death,
            left.reflected_birth + right.reflected_birth,
            left.reflected_death + right.reflected_death,
            left.selected_bands + right.selected_bands,
        )
        for position, left, right in zip(
            first.positions, first.output_orbits, later.output_orbits, strict=True
        )
    )
    words: list[RingPhaseHarmonic] = []
    for left, right in zip(first.bank_words, later.bank_words, strict=True):
        if (left.position, left.channel) != (right.position, right.channel):
            raise ValueError("temporal ring outputs have incompatible channel order")
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS,
            len(left.lanes) + len(right.lanes),
        )
        lanes = left.lanes + right.lanes
        words.append(
            RingPhaseHarmonic(
                left.position,
                left.channel,
                lanes,
                f5_modes(lanes),
                finite_output_period(lanes),
            )
        )
    result = tuple(words)
    pairs = tuple(
        a + b[1:]
        for a, b in zip(first.phase_pair_domains, later.phase_pair_domains, strict=True)
    )
    macro = None
    try:
        from .macro_conditioned_harmonics import authorize_finite_macro_window

        macro = authorize_finite_macro_window(
            first.certificate,
            start=first.start,
            duration=first.duration + later.duration,
        ).action
    except ValueError:
        pass  # Matching width does not prove an outer border return.
    combined_carry_phases = first.carry_wire_phases + later.carry_wire_phases
    duration = first.duration + later.duration
    return TemporalRingBankPayload(
        start=first.start,
        duration=duration,
        positions=first.positions,
        widths=first.widths + later.widths[1:],
        output_orbits=orbits,
        phase_pair_domains=pairs,
        bank_words=result,
        finite_moore_classes=finite_future_classes(
            result,
            duration,
            center_domains=combined_centers,
            global_residues99=combined_mod99,
            global_residues198=combined_mod198,
            carry_wire_phases=combined_carry_phases,
            on_lane_visit=lambda: ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
            ),
        ),
        macro=macro,
        rounds=max(first.rounds, later.rounds),
        carry_wire_phases=combined_carry_phases,
        center_domains=combined_centers,
        global_residues99=combined_mod99,
        global_residues198=combined_mod198,
    )


__all__ = ["compose_temporal_ring_bank_payload"]
