"""Finite-source construction and publication for reverse/add temporal rings.

Kept separate from the public bank contract so the family module remains a
small owner of the issued result and its consumers.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.polynomials.polynomial import f5_modes
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from .macro_conditioned_harmonics import inward_orbit_at
from .temporal_ring_channels import (
    TEMPORAL_RING_CHANNELS,
    ring_channel_lanes,
)
from .temporal_ring_harmonics import (
    ReverseAddTemporalRingBank,
    ReverseTemporalRingRefused,
    RingPhaseHarmonic,
    TemporalRingBankPayload,
    finite_future_classes,
    finite_output_period,
)

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_controlled_gt_bank import SourceGuardedGTBankAction


def authorize_temporal_ring_bank(
    certificate: CertifiedBorderGrowth,
    *,
    start: int = 0,
    duration: int | None = None,
    positions: tuple[int, ...] = (0,),
    source_pair_prefix: int = 0,
    include_source_digits: bool = False,
    max_cells: int = 16384,
    bank_action: SourceGuardedGTBankAction | None = None,
) -> ReverseAddTemporalRingBank:
    """Source-certify finite macro-specific harmonics at *any* inward positions.

    No periodic source hypothesis, fixed period<=8, or literal `2rev10` clock
    is required. Every certified multi-digit border edge constrains one
    correlated low->middle->high carry circuit. The digit/Q19 F5/borrow
    restrictions are propagated forward AND backward across physical ticks.
    """
    return certificate.owner.authorize_certified_temporal_ring_bank(
        certificate,
        start=start,
        duration=duration,
        positions=positions,
        source_pair_prefix=source_pair_prefix,
        include_source_digits=include_source_digits,
        max_cells=max_cells,
        bank_action=bank_action,
    )


def build_temporal_ring_bank_payload(
    certificate: CertifiedBorderGrowth,
    *,
    start: int,
    duration: int | None,
    positions: tuple[int, ...],
    source_pair_prefix: int,
    include_source_digits: bool,
    max_cells: int,
    bank_action: SourceGuardedGTBankAction | None,
) -> TemporalRingBankPayload:
    """Validate a source request and return its derived payload without issuing."""
    certificate.validate(certificate.owner, certificate.source)
    if (
        type(start) is not int
        or start < 0
        or type(positions) is not tuple
        or not positions
        or any(type(i) is not int or i < 0 for i in positions)
        or len(positions) > 64
        or len(set(positions)) != len(positions)
    ):
        raise ValueError("invalid temporal macro range or ring positions")
    if duration is not None and (type(duration) is not int or duration < 1):
        raise ValueError("temporal ring duration must be a positive integer")
    if type(max_cells) is not int or not 1 <= max_cells <= 16384:
        raise ValueError("temporal ring cell budget must be in 1..16384")
    if type(include_source_digits) is not bool:
        raise TypeError("source digit inclusion flag must be Boolean")
    if type(source_pair_prefix) is not int or source_pair_prefix < 0:
        raise ValueError("invalid source-pair prefix")
    skip = int(certificate.source is not certificate.owner.initial)
    initial_width = (
        certificate.source.output_width if skip else certificate.source.pair_width
    )
    if source_pair_prefix > (initial_width + 1) // 2:
        raise ValueError("source-pair probe reaches beyond center")
    if bank_action is not None:
        from .q19_controlled_gt_bank import SourceGuardedGTBankAction

        if type(bank_action) is not SourceGuardedGTBankAction:
            raise TypeError("temporal ring requires a source-issued GT bank action")
        bank_action.validate_source_authority()
        action_certificate = bank_action.border_certificate
        if (
            not bank_action.control_certified
            or action_certificate is not certificate
            or bank_action.owner is not certificate.owner
            or bank_action.source is not certificate.source
            or bank_action.growth_control != certificate.growth_word
            or bank_action.steps != len(certificate.growth_word)
        ):
            raise ValueError("GT bank action does not match this border certificate")
        if action_certificate is None:
            raise AssertionError("validated bank action lost its border certificate")
    stop = len(certificate.growth_word) if duration is None else start + duration
    if type(stop) is not int or not start < stop <= len(certificate.growth_word):
        raise ReverseTemporalRingRefused(
            "ring exceeds the finite source-certified horizon"
        )
    if start < skip:
        raise ReverseTemporalRingRefused(
            "later Q19 occurrence's consumed growth is outside the ring window"
        )
    width = initial_width + sum(certificate.growth_word[skip:start])
    widths = [initial_width]
    for growth in certificate.growth_word[skip:]:
        widths.append(widths[-1] + growth)
    for j in range(start, stop):
        if any(position >= (width + 1) // 2 for position in positions):
            raise ReverseTemporalRingRefused(
                "ring position crosses the moving pair center"
            )
        width += certificate.growth_word[j]
    domain_cells = sum(widths)
    if domain_cells > max_cells:
        raise ValueError("requires finite, positive nonshrinking width tape")
    carry_cells = sum(w + 1 for w in widths[:-1])
    borrow_cells = sum(
        max(widths[t], widths[t + 1]) + 1 for t in range(len(widths) - 1)
    )
    certificate.owner.ledger.bump(
        _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_CONSTRAINT_CELLS,
        domain_cells + carry_cells + borrow_cells,
    )
    system = certificate.inward_temporal_constraints(
        max_cells=max_cells,
        source_pair_prefix=source_pair_prefix,
        include_source_digits=include_source_digits,
    )
    # Source-bound K-digit windows provide strictly stronger carry safety
    # than the one-digit border. Unproved windows are kept conditional.
    windows = certificate.bilateral_window_ports()
    coarse = certificate.bilateral_carry_ports()
    for j in range(start, stop):
        t = j - skip
        width = system.widths[t]
        # Apply both the unit border and the stronger admitted K-digit
        # window when available. The larger port refines the same inward
        # transfer factor; it does not replace or weaken the unit boundary.
        for port in (coarse[j], windows[j]):
            if port is not None and width >= 2 * port.source.k + 1:
                system.constrain_bilateral_port(t, port)
    # The finite trace's outer return may be compiled with the same 96-cycle
    # exact homogeneous F5 action, but its *forcing* remains conditional.
    macro = None
    if (
        certificate.outer_pairs
        and all(pair is not None for pair in certificate.outer_pairs[start : stop + 1])
        and certificate.outer_pairs[start] == certificate.outer_pairs[stop]
    ):
        from .macro_conditioned_harmonics import authorize_finite_macro_window

        macro = authorize_finite_macro_window(
            certificate, start=start, duration=stop - start
        ).action
        system.constrain_macro_cycle(macro.cycle, start=start - skip)
    # A source-issued periodic bank already provides a complete, source-
    # aligned temporal output at its protected coordinate. Feed that action
    # BACK into the bilateral finite constraint system before propagation:
    # downstream F5/carry/bank masks must consume the same authenticated
    # coefficients instead of recomputing unrelated coarse domain guesses.
    # Only the specific owner-guarded coordinate is authorized here. No
    # extrapolation to adjacent positions, changing periods or future repeats.
    if bank_action is not None:
        position = bank_action.coordinate
        if position in positions:
            for j in range(start, stop + 1):
                source_time = j - skip
                if source_time < 0:
                    continue
                if position >= (system.widths[source_time] + 1) // 2:
                    raise ReverseTemporalRingRefused(
                        "GT bank coordinate reached the moving pair center"
                    )
                system.constrain_pair(source_time, position, bank_action.at(j))
    system.propagate(
        on_round=lambda: certificate.owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_PROPAGATION_ROUNDS
        )
    )
    duration = stop - start
    # Preserve the same-source K=1/K>1 correlated phase contracts rather
    # than publishing independent GT/F5 and carry output projections.
    from .temporal_carry_phase import CertifiedCarryPhase

    carry_phases: list[tuple[CertifiedCarryPhase, ...]] = []
    for j in range(start, stop):
        physical_t = j - skip
        chosen: dict[int, CertifiedCarryPhase] = {}
        for port in (coarse[j], windows[j]):
            if (
                port is not None
                and port.source.k
                in system.represented_middle_constraint_keys(physical_t)
            ):
                chosen[port.source.k] = CertifiedCarryPhase(
                    j,
                    system.widths[physical_t],
                    port,
                    system.middle_carry_wire(physical_t, port.source.k),
                )
        carry_phases.append(tuple(chosen[k] for k in sorted(chosen)))
    center_domains = tuple(
        system.center_domain(t) for t in range(start - skip, stop - skip + 1)
    )
    residues99 = tuple(
        system.global_residue99(t) for t in range(start - skip, stop - skip + 1)
    )
    residues198 = tuple(
        system.global_residue198(t) for t in range(start - skip, stop - skip + 1)
    )
    orbits = tuple(
        inward_orbit_at(system, start - skip, duration, i) for i in positions
    )
    phase_pairs = tuple(
        tuple(system.pair_domain(t, i) for t in range(start - skip, stop - skip + 1))
        for i in positions
    )
    outputs: list[RingPhaseHarmonic] = []
    for position, orbit in zip(positions, orbits, strict=True):
        for channel in TEMPORAL_RING_CHANNELS:
            bits = ring_channel_lanes(orbit, channel)
            certificate.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS,
                len(bits),
            )
            outputs.append(
                RingPhaseHarmonic(
                    position,
                    channel,
                    bits,
                    f5_modes(bits),
                    finite_output_period(bits),
                )
            )
    words = tuple(outputs)
    payload = TemporalRingBankPayload(
        start=start,
        duration=duration,
        positions=positions,
        widths=system.widths[start - skip : stop - skip + 1],
        output_orbits=orbits,
        phase_pair_domains=phase_pairs,
        bank_words=words,
        finite_moore_classes=finite_future_classes(
            words,
            duration,
            center_domains=center_domains,
            global_residues99=residues99,
            global_residues198=residues198,
            carry_wire_phases=tuple(carry_phases),
            on_lane_visit=lambda: certificate.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
            ),
        ),
        macro=macro,
        rounds=system.rounds,
        carry_wire_phases=tuple(carry_phases),
        center_domains=center_domains,
        global_residues99=residues99,
        global_residues198=residues198,
    )
    return payload


__all__ = [
    "authorize_temporal_ring_bank",
    "build_temporal_ring_bank_payload",
]
