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

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
        SourceWeightedTriplingAction,
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
