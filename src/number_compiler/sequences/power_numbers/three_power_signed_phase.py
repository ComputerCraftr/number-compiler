"""Demanded positional counts of an authenticated bilateral tripling source.

The position clock is not the physical tripling clock. Unknown intervals retain
integer capacities; they never supply a prime verdict or a repeated source word.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.signed_phase import (
    BinaryPhaseCarryAction,
    SymbolicPhaseInterval,
    phase_add,
    phase_rotate,
    signed_phase_fold,
)
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_payload,
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
    FermatOuterInnerPhaseConstraint,
    demand_outer_inner_phase_constraint,
)
from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
    _terminal_status_from_signed_folds,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
        SourceWeightedTriplingAction,
    )
    from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
        FermatTwoSidedSourceCylinder,
    )


@dataclass(frozen=True, slots=True)
class KnownPhaseSegment:
    """Local arithmetic plus the producing source's admitted carry edges."""

    start: int
    action: BinaryPhaseCarryAction
    admitted_edges: tuple[tuple[int, int], ...]


@dataclass(frozen=True, slots=True, weakref_slot=True)
class SourceSignedPhaseCountPort:
    """Exact-instance issued counts; arithmetic equality alone is not authority."""

    source_index: int
    source_level: int
    source_width: int
    fold_width: int
    known_counts: tuple[int, ...]
    known_segments: tuple[KnownPhaseSegment, ...]
    unknown_intervals: tuple[SymbolicPhaseInterval, ...]
    _issuer: object = None

    def verify(self) -> None:
        if not harmonic_verified(self, harmonic_payload(self), issuer=_PHASE_ISSUER):
            raise ValueError("unissued or modified signed phase source port")

    @property
    def known_signed_fold(self) -> int:
        self.verify()
        return signed_phase_fold(self.known_counts, self.fold_width)

    @property
    def exact_complete_fold(self) -> int | None:
        self.verify()
        return (
            signed_phase_fold(self.known_counts, self.fold_width)
            if not self.unknown_intervals
            else None
        )

    @property
    def symbolic_unknown_site_count(self) -> int:
        self.verify()
        return sum(block.width for block in self.unknown_intervals)


_PHASE_ISSUER = new_harmonic_issuer(SourceSignedPhaseCountPort)


def demand_signed_phase_counts(
    source: SourceWeightedTriplingAction,
) -> SourceSignedPhaseCountPort:
    """Construct only from a complete, authenticated source partition."""
    if not source.producer_verified:
        raise ValueError("unissued signed border action")
    width = source.fold_width
    if width > 8192:
        raise ValueError("signed phase demand exceeds explicit phase budget")
    if len(source.blocks) * 14 * width > 80_000:
        raise ValueError("signed phase demand exceeds retained cell budget")
    known = (0,) * (2 * width)
    segments: list[KnownPhaseSegment] = []
    unknown: list[SymbolicPhaseInterval] = []
    cursor = 0
    for block, edges in zip(source.blocks, source.admissible_edges, strict=True):
        if block.start != cursor:
            raise ArithmeticError("source phase partition has a gap or overlap")
        cursor += block.width
        if block.source_value is None:
            unknown.append(
                SymbolicPhaseInterval.from_interval(block.start, block.width, width)
            )
        else:
            action = BinaryPhaseCarryAction.from_word(
                block.source_value, block.width, width
            )
            if not edges or any(
                ci not in (0, 1, 2) or co != action.carry_out[ci] for ci, co in edges
            ):
                raise ArithmeticError("source carry edges disagree with phase action")
            segments.append(KnownPhaseSegment(block.start, action, edges))
            known = phase_add(known, phase_rotate(action.source_counts, block.start))
    if cursor != source.origin.bilateral.binary.source_digits:
        raise ArithmeticError("source phase partition omits its terminal extent")
    if signed_phase_fold(known, width) != source.source_signed_known_sum:
        raise ArithmeticError("phase projection disagrees with source signed fold")
    result = SourceSignedPhaseCountPort(
        source.index,
        source.level,
        cursor,
        width,
        known,
        tuple(segments),
        tuple(unknown),
    )
    issue_harmonic(result, harmonic_payload(result), issuer=_PHASE_ISSUER)
    return result


@dataclass(frozen=True, slots=True, weakref_slot=True)
class SourceRestrictedPhaseRelation:
    """One issued join of signed phase capacities and two-sided source guards.

    Boundaries are *ordinary tripling* carry ingress indices (absolute binary
    digit positions).  An unenumerated middle is never assigned exact counts.
    """

    phase: SourceSignedPhaseCountPort
    cylinder: FermatTwoSidedSourceCylinder
    boundary_domains: tuple[tuple[int, tuple[int, ...]], ...]
    complete_histograms: tuple[tuple[int, ...], ...] | None
    outer_inner: FermatOuterInnerPhaseConstraint
    _issuer: object = None

    @property
    def producer_verified(self) -> bool:
        try:
            self.phase.verify()
        except ValueError:
            return False
        return (
            self.cylinder.producer_verified
            and self.outer_inner.producer_verified
            and harmonic_verified(self, self._payload(), issuer=_JOINT_PHASE_ISSUER)
        )

    def _payload(self) -> tuple[object, ...]:
        return (
            harmonic_payload(self.phase),
            self.cylinder._payload(),
            self.boundary_domains,
            self.complete_histograms,
            self.outer_inner._payload(),
        )

    @property
    def source_to_global_fold_proven(self) -> bool:
        """Only when all admitted complete source fibers have one residue."""
        if not self.producer_verified:
            raise ValueError("unissued or changed source-restricted phase relation")
        if self.complete_histograms is None:
            return False
        return (
            len(
                {
                    signed_phase_fold(row, self.phase.fold_width)
                    for row in self.complete_histograms
                }
            )
            == 1
        )

    @property
    def complete_signed_fold(self) -> int | None:
        if not self.source_to_global_fold_proven:
            return None
        assert self.complete_histograms is not None
        return signed_phase_fold(self.complete_histograms[0], self.phase.fold_width)

    def refine_inward(
        self,
        *,
        additional_binary_places: int = 1,
        additional_decimal_places: int = 0,
        inward_boundaries: int = 8,
    ) -> SourceRestrictedPhaseRelation:
        """Reissue one deeper certified source cone at the first open inlet."""
        if not self.producer_verified:
            raise ValueError("unissued source-restricted refinement")
        refined = self.cylinder.source.demand_inward_source_refinement(
            additional_binary_places=additional_binary_places,
            additional_decimal_places=additional_decimal_places,
        )
        return refined.demand_source_restricted_phase_relation(
            inward_boundaries=inward_boundaries
        )

    @property
    def terminal_status(self) -> str:
        if not self.producer_verified:
            raise ValueError("unissued or changed source-restricted phase relation")
        histograms = self.complete_histograms
        if histograms is None:
            return "UNKNOWN"
        signed_folds = tuple(
            signed_phase_fold(row, self.phase.fold_width) for row in histograms
        )
        return _terminal_status_from_signed_folds(
            self.cylinder.source.level, self.phase.fold_width, signed_folds
        )


_JOINT_PHASE_ISSUER = new_harmonic_issuer(SourceRestrictedPhaseRelation)


def demand_source_restricted_phase_relation(
    source: SourceWeightedTriplingAction,
    *,
    max_fibers: int = 64,
    inward_boundaries: int = 8,
) -> SourceRestrictedPhaseRelation:
    """Join the cyclotomic/Sturmian source cylinder with its 2w phase count.

    Per-position carry domains are derived from the exact binary/decimal CRT
    source and admitted high edge guards, not independent sampled masks.
    The source's enormous interior stays open unless a full finite fiber is
    provable; an observed reset can never erase a phase-count unknown.
    """
    if type(max_fibers) is not int or not 1 <= max_fibers <= 4096:
        raise ValueError("invalid exact source fiber budget")
    if type(inward_boundaries) is not int or not 0 <= inward_boundaries <= 64:
        raise ValueError("invalid source inward-boundary budget")
    phase = source.demand_signed_phase_count_port()
    cylinder = source.demand_two_sided_source_cylinder()
    if not cylinder.producer_verified:
        raise ValueError("unissued two-sided source cylinder")
    high_start = source.blocks[-1].start
    total = phase.source_width
    B = cylinder.binary_low_bits
    boundaries = {0, total, high_start, min(B, total)}
    boundaries.update(min(total, B + d) for d in range(1, inward_boundaries + 1))
    boundaries.update(block.start for block in source.blocks)
    domains = tuple(
        (j, cylinder.ingress_options(j, max_fibers)) for j in sorted(boundaries)
    )
    fibers = cylinder.bounded_phase_fibers(max_fibers)
    hist = None if fibers is None else tuple(f.source_phase_counts for f in fibers)
    outer_inner = demand_outer_inner_phase_constraint(source, cylinder)
    if outer_inner.project_known_fold() != phase.known_signed_fold:
        raise ArithmeticError(
            "joint cyclotomic projection lost known signed phase counts"
        )
    if hist is not None:
        for row in hist:
            # Every complete fiber projects to the same global source orbit.
            # This is a cross-domain check, not an assumption of forced counts.
            if len(row) != 2 * source.fold_width:
                raise ArithmeticError("signed phase fiber width mismatch")
    joint = SourceRestrictedPhaseRelation(phase, cylinder, domains, hist, outer_inner)
    issue_harmonic(joint, joint._payload(), issuer=_JOINT_PHASE_ISSUER)
    return joint
