"""Finite-source construction and publication for reverse/add temporal rings.

Kept separate from the public bank contract so the family module remains a
small owner of the issued result and its consumers.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from ._q19_issuance import issue_q19_record
from .macro_conditioned_harmonics import _inward_orbit_at
from .temporal_inward_constraints import ReverseInwardConstraints
from .temporal_ring_harmonics import (
    _BANKS,
    _ISSUER,
    _RING_CHANNELS,
    ReverseAddTemporalRingBank,
    ReverseTemporalRingRefused,
    RingPhaseHarmonic,
    _finite_period,
    _scalar_harmonics,
)

if TYPE_CHECKING:
    from .border_carry_safety import BilateralCyclePort
    from .macro_conditioned_harmonics import CycleHarmonicAction, MacroPhaseInwardOrbit
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_controlled_gt_bank import SourceGuardedGTBankAction
    from .temporal_carry_phase import CertifiedCarryPhase


def _finite_future_classes(
    words: tuple[RingPhaseHarmonic, ...],
    duration: int,
    *,
    center_domains: tuple[tuple[int, ...], ...] = (),
    global_residues99: tuple[int | None, ...] = (),
    global_residues198: tuple[int | None, ...] = (),
    carry_wire_phases: tuple[tuple[CertifiedCarryPhase, ...], ...] = (),
    on_lane_visit: Callable[[], None] | None = None,
) -> tuple[int, ...]:
    """Intern local suffix signatures on the finite certified path only.

    Unlike the `2rev10` source-input Moore automaton, these labels have NO
    defined transition beyond the finite final row. IDs are local diagnostic
    labels, not portable semantic IDs, and cannot power a complete-root
    action.
    """
    codes: dict[tuple[object, ...], int] = {}
    result = [0] * (duration + 1)
    for t in range(duration - 1, -1, -1):
        lane_values = []
        for word in words:
            if on_lane_visit is not None:
                on_lane_visit()
            lane_values.append(word.lanes[t])
        joint = (
            (center_domains[t], center_domains[t + 1]) if center_domains else (),
            (global_residues99[t], global_residues99[t + 1])
            if global_residues99
            else (),
            (global_residues198[t], global_residues198[t + 1])
            if global_residues198
            else (),
            _carry_phase_observation(carry_wire_phases[t]) if carry_wire_phases else (),
        )
        signature = (tuple(lane_values), joint, result[t + 1])
        result[t] = codes.setdefault(signature, len(codes) + 1)
    return tuple(result)


def _carry_phase_observation(
    phases: tuple[CertifiedCarryPhase, ...],
) -> tuple[object, ...]:
    """Exact demanded carry/F5 output for one finite row, independent of ID."""
    return tuple(
        (
            phase.port.source.k,
            phase.port.growth,
            phase.low_carry,
            phase.high_carries,
            phase.middle_transfers,
            phase.first_reset_witnesses,
            phase.conditional_f5,
        )
        for phase in phases
    )


def _restrict_bilateral_port(
    system: ReverseInwardConstraints,
    t: int,
    k: int,
    port: BilateralCyclePort,
    source_width: int,
) -> None:
    """Intersect low overflow, one shared middle map and high ingress."""
    system.constrain_bilateral_port(t, port)


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
        bank_action._validate()
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
    try:
        return _build_temporal_ring_bank(
            certificate,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            include_source_digits=include_source_digits,
            max_cells=max_cells,
            bank_action=bank_action,
            skip=skip,
            initial_width=initial_width,
        )
    except Exception:
        certificate.owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES
        )
        raise


def _build_temporal_ring_bank(
    certificate: CertifiedBorderGrowth,
    *,
    start: int,
    duration: int | None,
    positions: tuple[int, ...],
    source_pair_prefix: int,
    include_source_digits: bool,
    max_cells: int,
    bank_action: SourceGuardedGTBankAction | None,
    skip: int,
    initial_width: int,
) -> ReverseAddTemporalRingBank:
    """Run a prevalidated request and charge only work reached by execution."""
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
                _restrict_bilateral_port(system, t, port.source.k, port, width)
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
        chosen = {}
        for port in (coarse[j], windows[j]):
            if (
                port is not None
                and (physical_t, port.source.k) in system._middle_transfers
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
        _inward_orbit_at(system, start - skip, duration, i) for i in positions
    )
    phase_pairs = tuple(
        tuple(system.pair_domain(t, i) for t in range(start - skip, stop - skip + 1))
        for i in positions
    )
    outputs: list[RingPhaseHarmonic] = []
    for position, orbit in zip(positions, orbits, strict=True):
        for channel in _RING_CHANNELS:
            if channel in _BANKS:
                bit_rows: list[int | None] = []
                for bands in orbit.selected_bands:
                    certificate.owner.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
                    )
                    possible = {int(channel == band) for band in bands}
                    bit_rows.append(
                        next(iter(possible)) if len(possible) == 1 else None
                    )
                bits = tuple(bit_rows)
            else:
                values = {
                    "f5": orbit.pair_f5,
                    "low_carry": orbit.low_carries,
                    "reflected_carry": orbit.reflected_carries,
                    "raw_borrow": orbit.raw_innovation_borrow,
                    "carry_xor": orbit.reflected_xor,
                    "carry_borrow_xor": orbit.carry_borrow_xor,
                    "low_birth": orbit.low_birth,
                    "low_death": orbit.low_death,
                    "high_birth": orbit.reflected_birth,
                    "high_death": orbit.reflected_death,
                }[channel]
                bit_rows = []
                for row in values:
                    certificate.owner.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
                    )
                    bit_rows.append(row[0] if len(row) == 1 else None)
                bits = tuple(bit_rows)
            outputs.append(
                RingPhaseHarmonic(
                    position,
                    channel,
                    bits,
                    _scalar_harmonics(bits),
                    _finite_period(bits),
                )
            )
    words = tuple(outputs)
    return _issue_temporal_ring_bank(
        certificate,
        start=start,
        duration=duration,
        positions=positions,
        widths=system.widths[start - skip : stop - skip + 1],
        output_orbits=orbits,
        phase_pair_domains=phase_pairs,
        bank_words=words,
        finite_moore_classes=_finite_future_classes(
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


def _issue_temporal_ring_bank(
    certificate: CertifiedBorderGrowth,
    *,
    start: int,
    duration: int,
    positions: tuple[int, ...],
    widths: tuple[int, ...],
    output_orbits: tuple[MacroPhaseInwardOrbit, ...],
    phase_pair_domains: tuple[tuple[tuple[int, ...], ...], ...],
    bank_words: tuple[RingPhaseHarmonic, ...],
    finite_moore_classes: tuple[int, ...],
    macro: CycleHarmonicAction | None,
    rounds: int,
    carry_wire_phases: tuple[tuple[CertifiedCarryPhase, ...], ...],
    center_domains: tuple[tuple[int, ...], ...],
    global_residues99: tuple[int | None, ...],
    global_residues198: tuple[int | None, ...],
) -> ReverseAddTemporalRingBank:
    """Publish one owner-retained snapshot after exact source computation."""
    owner = certificate.owner
    certificate.validate(owner, certificate.source)
    registry = owner._issuance_registry
    key = registry.allocate_temporal_ring_bank_key()
    record = object.__new__(ReverseAddTemporalRingBank)
    values = {
        "certificate": certificate,
        "start": start,
        "duration": duration,
        "positions": positions,
        "widths": widths,
        "output_orbits": output_orbits,
        "phase_pair_domains": phase_pair_domains,
        "bank_words": bank_words,
        "finite_moore_classes": finite_moore_classes,
        "macro": macro,
        "rounds": rounds,
        "carry_wire_phases": carry_wire_phases,
        "center_domains": center_domains,
        "global_residues99": global_residues99,
        "global_residues198": global_residues198,
        "complete_integer_certified": False,
        "temporal_repeat_certified": False,
        "_registry_key": key,
    }
    issue_q19_record(record, values, _ISSUER)
    registry.retain_temporal_ring_bank(key, record)
    try:
        record.__post_init__()
    except BaseException:
        registry.discard_temporal_ring_bank(key, record)
        raise
    return record
