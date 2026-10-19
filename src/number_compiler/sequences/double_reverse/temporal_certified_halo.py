"""Source-authenticated shrinking-halo transitions for finite 2rev10 windows."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
    issue_source_record,
    validate_source_record,
)
from .stencil_moore import stencil_cell
from .temporal_birth_ring import BirthRingPorts, BirthRingState, odd_boundary_pairs
from .temporal_hashlife import growth_ports

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource


class SourceConditionedDepthWindowUnavailable(ValueError):
    """Expected refusal while preparing a finite source-conditioned window."""


def ring_outer(state: BirthRingState, pairs: int) -> BirthRingState:
    return BirthRingState(state.left[:pairs], state.right[-pairs:], state.phase)


def ring_next_pair(state: BirthRingState, pairs: int) -> tuple[int, int]:
    return state.left[pairs], state.right[-1 - pairs]


def _advance_halo_without_frames(state: BirthRingState) -> BirthRingState:
    """Advance a finite halo with zero padding beyond its proven causal cone."""
    size = state.pairs
    born_left, born_right = growth_ports(state.phase, 1)

    def left(index: int) -> int:
        return state.left[index] if 0 <= index < size else 0

    def right(index: int) -> int:
        return state.right[index] if 0 <= index < size else 0

    return BirthRingState(
        tuple(
            stencil_cell(
                left(j - born_left - 1),
                left(j - born_left),
                left(j - born_left + 1),
            )
            for j in range(size)
        ),
        tuple(
            stencil_cell(
                right(j + born_right - 1),
                right(j + born_right),
                right(j + born_right + 1),
            )
            for j in range(size)
        ),
        (state.phase + 2) % 4,
    )


@dataclass(frozen=True, slots=True)
class CertifiedHalo:
    """A finite halo whose retained precision shrinks on each F tick.

    The stored state contains only digits currently certified by the source.
    Zero-padding may be used internally to evaluate the radius-one stencil,
    but the uncertified inward edge is discarded before returning a successor.
    """

    state: BirthRingState
    certified_pairs: int
    f_offset: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.state) is not BirthRingState
            or type(self.certified_pairs) is not int
            or self.certified_pairs != self.state.pairs
            or type(self.f_offset) is not int
            or self.f_offset < 0
        ):
            raise ValueError("invalid precision-labelled source halo")

    def outer(self, pairs: int) -> BirthRingState:
        if type(pairs) is not int or not 1 <= pairs <= self.certified_pairs:
            raise ValueError("requested halo digits are not source-certified")
        return ring_outer(self.state, pairs)

    def step(self) -> CertifiedHalo:
        """Apply the exact graded transition H_L -> H_(L-1)."""
        if self.certified_pairs < 2:
            raise ValueError("cannot step without a certified inward carry port")
        evolved = _advance_halo_without_frames(self.state)
        retained = ring_outer(evolved, self.certified_pairs - 1)
        return CertifiedHalo(retained, self.certified_pairs - 1, self.f_offset + 1)

    def refill(self, authentic: BirthRingState) -> CertifiedHalo:
        """Accept a source-authenticated refill only after checking overlap.

        The caller must obtain ``authentic`` from its validated source cursor.
        This method checks phase and every retained digit before resetting the
        precision label to the width of that freshly authenticated slice.
        """
        if (
            type(authentic) is not BirthRingState
            or authentic.phase != self.state.phase
            or authentic.pairs < self.certified_pairs
        ):
            raise ValueError("incompatible authenticated halo continuation")
        retained = self.certified_pairs
        if (
            authentic.left[:retained] != self.state.left
            or authentic.right[-retained:] != self.state.right
        ):
            raise ArithmeticError("authenticated continuation disagrees with halo")
        return CertifiedHalo(authentic, authentic.pairs, self.f_offset)


def halo_outer_odd_row(
    halo: CertifiedHalo, outer_pairs: int
) -> tuple[BirthRingState, tuple[tuple[int, int], ...] | None]:
    """Read one certified even/odd boundary row from a retained halo."""
    if (
        type(halo) is not CertifiedHalo
        or type(outer_pairs) is not int
        or outer_pairs < 1
        or halo.certified_pairs < outer_pairs + 2
    ):
        raise ValueError("odd boundary row needs one certified inward pair")
    outer = halo.outer(outer_pairs + 1)
    inlet = BirthRingPorts(
        halo.state.left[outer_pairs + 1],
        halo.state.right[-outer_pairs - 2],
    )
    return outer, odd_boundary_pairs(outer, inlet)


@dataclass(frozen=True, slots=True)
class SourceContinuedHaloTrace(SourceAuthorizedRecord):
    """Finite halo trace whose refills come from one prepared source cursor."""

    physical_prefix: int
    source_root: int
    source_phase: int
    source_horizon: int
    start_f_steps: int
    outer_pairs: int
    f_steps: int
    block_f_steps: int
    even_outer: tuple[BirthRingState, ...]
    odd_outer: tuple[tuple[tuple[int, int], ...] | None, ...]
    refill_offsets: tuple[int, ...]
    minimum_certified_pairs: int
    maximum_halo_pairs: int

    def validate_source_authority(self) -> SourceRecordAuthority:
        authority = validate_source_record(self)
        expected_refills = tuple(
            self.start_f_steps + offset
            for offset in range(self.block_f_steps, self.f_steps, self.block_f_steps)
        )
        if (
            type(self.physical_prefix) is not int
            or type(self.source_root) is not int
            or authority.root != self.source_root
            or authority.source_generation != self.physical_prefix
            or type(self.source_phase) is not int
            or self.source_phase not in (0, 1, 2, 3)
            or type(self.source_horizon) is not int
            or self.source_horizon < 1
            or type(self.start_f_steps) is not int
            or self.start_f_steps < 0
            or type(self.outer_pairs) is not int
            or self.outer_pairs < 1
            or type(self.f_steps) is not int
            or not 1 <= self.f_steps <= 4
            or type(self.block_f_steps) is not int
            or not 1 <= self.block_f_steps <= 4
            or self.start_f_steps + self.f_steps > self.source_horizon
            or type(self.even_outer) is not tuple
            or len(self.even_outer) != self.f_steps + 1
            or any(
                type(state) is not BirthRingState
                or state.pairs != self.outer_pairs + 1
                or state.phase
                != (self.source_phase + 2 * (self.start_f_steps + tick)) % 4
                for tick, state in enumerate(self.even_outer)
            )
            or type(self.odd_outer) is not tuple
            or len(self.odd_outer) != self.f_steps
            or any(
                row is not None
                and (
                    type(row) is not tuple
                    or len(row) != self.outer_pairs + 1
                    or any(
                        type(pair) is not tuple
                        or len(pair) != 2
                        or any(
                            type(digit) is not int or not 0 <= digit <= 9
                            for digit in pair
                        )
                        for pair in row
                    )
                )
                for row in self.odd_outer
            )
            or type(self.refill_offsets) is not tuple
            or any(type(offset) is not int for offset in self.refill_offsets)
            or self.refill_offsets != expected_refills
            or type(self.minimum_certified_pairs) is not int
            or self.minimum_certified_pairs != self.outer_pairs + 1
            or type(self.maximum_halo_pairs) is not int
            or self.maximum_halo_pairs
            != self.outer_pairs + 1 + min(self.block_f_steps, self.f_steps)
        ):
            raise ValueError("invalid source-backed halo continuation authority")
        return authority

    def to_packet(self) -> dict[str, object]:
        self.validate_source_authority()
        start = self.physical_prefix + 2 * self.start_f_steps
        return {
            "status": "available",
            "mode": "finite_source_backed_certified_halo",
            "relation_semantics": "exact_pointed_source_continuation",
            "physical_interval": [start, start + 2 * self.f_steps],
            "outer_pairs": self.outer_pairs,
            "f_steps": self.f_steps,
            "block_f_steps": self.block_f_steps,
            "refill_offsets_f_steps": list(self.refill_offsets),
            "overlap_verified_on_every_refill": True,
            "minimum_certified_pairs": self.minimum_certified_pairs,
            "maximum_halo_pairs": self.maximum_halo_pairs,
            "complete_even_outer_trace": [
                {
                    "phase": state.phase,
                    "left": list(state.left),
                    "right": list(state.right),
                }
                for state in self.even_outer
            ],
            "complete_odd_outer_trace": [
                None if row is None else [list(pair) for pair in row]
                for row in self.odd_outer
            ],
            "source_root_assignment_joined": True,
            "infinite_period_certified": False,
        }


def _source_halo_at(
    source: PointedBankSource, f_offset: int, pairs: int
) -> BirthRingState:
    from .source_bound_bank import PointedBankSource as BankSource

    if type(source) is not BankSource:
        raise TypeError("halo continuation needs an existing PointedBankSource")
    if not 0 <= f_offset <= source.f_steps:
        raise SourceConditionedDepthWindowUnavailable(
            "halo continuation exceeds the prepared source horizon"
        )
    width = source.width_in + sum(growth_ports(source.phase, f_offset))
    if 2 * pairs > width:
        raise SourceConditionedDepthWindowUnavailable(
            "prepared source is too narrow for the requested causal halo"
        )
    left = source.engine.pointed_window(source.root, f_offset, source.phase, 0, pairs)
    right = source.engine.pointed_window(
        source.root, f_offset, source.phase, width - pairs, pairs
    )
    return BirthRingState(left, right, (source.phase + 2 * f_offset) % 4)


def build_source_continued_halo_trace(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int,
    block_f_steps: int,
) -> SourceContinuedHaloTrace:
    from .source_bound_bank import PointedBankSource as BankSource

    if type(source) is not BankSource:
        raise TypeError("halo continuation needs an existing PointedBankSource")
    source.validate(require_issued_cursor=source.f_steps > 0)
    if (
        type(outer_pairs) is not int
        or outer_pairs < 1
        or type(start_f_steps) is not int
        or start_f_steps < 0
        or type(f_steps) is not int
        or not 1 <= f_steps <= 4
        or type(block_f_steps) is not int
        or not 1 <= block_f_steps <= 4
        or start_f_steps + f_steps > source.f_steps
    ):
        raise SourceConditionedDepthWindowUnavailable(
            "continuation must fit the requested prepared-source horizon"
        )

    even: list[BirthRingState] = []
    odd: list[tuple[tuple[int, int], ...] | None] = []
    refill_offsets: list[int] = []
    minimum_precision = outer_pairs + 1
    maximum_halo = 0
    current: CertifiedHalo | None = None
    offset = 0
    while offset < f_steps:
        block = min(block_f_steps, f_steps - offset)
        required = outer_pairs + 1 + block
        if current is None:
            initial = _source_halo_at(source, start_f_steps, required)
            current = CertifiedHalo(initial, required)
            maximum_halo = max(maximum_halo, current.certified_pairs)
        elif current.certified_pairs < required:
            authentic = _source_halo_at(source, start_f_steps + offset, required)
            current = current.refill(authentic)
            refill_offsets.append(start_f_steps + offset)
            maximum_halo = max(maximum_halo, current.certified_pairs)

        for _ in range(block):
            state, odd_row = halo_outer_odd_row(current, outer_pairs)
            even.append(state)
            odd.append(odd_row)
            current = current.step()
            minimum_precision = min(minimum_precision, current.certified_pairs)
        offset += block

    if current is None:
        raise AssertionError("validated continuation did not produce a source halo")
    even.append(current.outer(outer_pairs + 1))
    record = SourceContinuedHaloTrace(
        source.physical_prefix,
        source.root,
        source.phase,
        source.f_steps,
        start_f_steps,
        outer_pairs,
        f_steps,
        block_f_steps,
        tuple(even),
        tuple(odd),
        tuple(refill_offsets),
        minimum_precision,
        maximum_halo,
    )
    issued = issue_source_record(
        record,
        source.arena,
        source.root,
        source_generation=source.physical_prefix,
    )
    issued.validate_source_authority()
    return issued


def source_continued_halo_trace_packet_from_source(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int,
    block_f_steps: int = 2,
) -> dict[str, object]:
    """Build and serialize a bounded trace from one prepared source cursor."""
    from .source_bound_bank import PointedBankSource as BankSource

    if type(source) is not BankSource:
        raise TypeError("halo continuation needs an existing PointedBankSource")
    with source.ledger.reservation(source.scratch_owner, entries=256, nodes=256):
        trace = build_source_continued_halo_trace(
            source,
            outer_pairs=outer_pairs,
            start_f_steps=start_f_steps,
            f_steps=f_steps,
            block_f_steps=block_f_steps,
        )
        return trace.to_packet()
