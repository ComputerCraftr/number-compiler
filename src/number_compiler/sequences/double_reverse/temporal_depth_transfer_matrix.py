"""Finite 100-state depth transfers for the 2rev10 moving boundary.

The unconditioned matrix is an exact all-inlet relation for one supplied
outer step. Its powers describe that conditional inlet program only. The
source-conditioned path fixes one wider initial halo and checks the complete
finite outer and odd-generation trace; it has no repeat or power operation.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from itertools import pairwise
from typing import TYPE_CHECKING, TypeVar, overload

from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanMatrix,
    BooleanStateSpace,
)

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
    issue_source_record,
    validate_source_record,
)
from .temporal_birth_ring import BirthRingPorts, BirthRingState, odd_boundary_pairs
from .temporal_certified_halo import (
    CertifiedHalo,
    SourceConditionedDepthWindowUnavailable,
    SourceContinuedHaloTrace,
    build_source_continued_halo_trace,
    halo_outer_odd_row,
    ring_next_pair,
    ring_outer,
    source_continued_halo_trace_packet_from_source,
)
from .temporal_hashlife import growth_ports

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource

_Published = TypeVar("_Published")

PAIR_COUNT = 100
ALL_PAIRS: tuple[tuple[int, int], ...] = tuple(
    (left, right) for left in range(10) for right in range(10)
)
_PAIR_STATE_SPACE: BooleanStateSpace[tuple[int, int]] = BooleanStateSpace(
    "double_reverse.decimal-pair", ALL_PAIRS
)


def pair_index(pair: tuple[int, int]) -> int:
    if (
        type(pair) is not tuple
        or len(pair) != 2
        or any(type(digit) is not int or not 0 <= digit <= 9 for digit in pair)
    ):
        raise ValueError("inward pair must consist of two decimal digits")
    return 10 * pair[0] + pair[1]


@dataclass(frozen=True, slots=True, init=False)
class BooleanPairMatrix:
    """Boolean relation owned by the double-reverse ordered-pair space."""

    _relation: BooleanMatrix[tuple[int, int]]

    def __init__(self, rows: tuple[int, ...]) -> None:
        object.__setattr__(self, "_relation", BooleanMatrix(_PAIR_STATE_SPACE, rows))

    @classmethod
    def _from_relation(
        cls, relation: BooleanMatrix[tuple[int, int]]
    ) -> BooleanPairMatrix:
        if (
            type(relation) is not BooleanMatrix
            or relation.state_space is not _PAIR_STATE_SPACE
        ):
            raise TypeError("double-reverse matrix needs its ordered-pair state space")
        result = object.__new__(cls)
        object.__setattr__(result, "_relation", relation)
        return result

    @property
    def rows(self) -> tuple[int, ...]:
        return self._relation.rows

    @property
    def state_space(self) -> BooleanStateSpace[tuple[int, int]]:
        return self._relation.state_space

    @classmethod
    def identity(cls) -> BooleanPairMatrix:
        return cls._from_relation(
            BooleanMatrix[tuple[int, int]].identity(_PAIR_STATE_SPACE)
        )

    def then(self, later: BooleanPairMatrix) -> BooleanPairMatrix:
        """Apply this matrix, then ``later``, in physical temporal order."""
        if type(later) is not BooleanPairMatrix:
            raise TypeError("matrix composition requires another BooleanPairMatrix")
        return self._from_relation(self._relation.then(later._relation))

    def power(self, count: int) -> BooleanPairMatrix:
        if type(count) is not int or count < 0 or count.bit_length() > 4096:
            raise ValueError("matrix exponent must be a nonnegative <=4096-bit integer")
        return self._from_relation(self._relation.power(count))

    def endpoints(self, initial_pair: tuple[int, int]) -> tuple[tuple[int, int], ...]:
        bits = self._relation.image(1 << pair_index(initial_pair))
        return tuple(ALL_PAIRS[i] for i in range(PAIR_COUNT) if bits >> i & 1)

    def transport(self, source_bitset: int) -> int:
        return self._relation.image(source_bitset)

    @property
    def edge_count(self) -> int:
        return sum(row.bit_count() for row in self.rows)

    @property
    def maximum_successors(self) -> int:
        return max((row.bit_count() for row in self.rows), default=0)


def outer_step_matrix(
    current: BirthRingState, following: BirthRingState
) -> BooleanPairMatrix:
    """Eliminate all next-depth inlet digits for one exact outer F-step."""
    if (
        type(current) is not BirthRingState
        or type(following) is not BirthRingState
        or current.pairs != following.pairs
        or following.phase != (current.phase + 2) % 4
    ):
        raise ValueError("outer step requires compatible moving-boundary rings")
    rows: list[int] = []
    for left, right in ALL_PAIRS:
        inlet = BirthRingPorts(left, right)
        if current.advance(inlet)[0] != following:
            rows.append(0)
            continue
        extended = BirthRingState(
            current.left + (left,), (right,) + current.right, current.phase
        )
        targets = 0
        for next_left in (0, 3):
            for next_right in (0, 5):
                evolved = extended.advance(BirthRingPorts(next_left, next_right))[0]
                if (evolved.left[:-1], evolved.right[1:], evolved.phase) != (
                    following.left,
                    following.right,
                    following.phase,
                ):
                    raise AssertionError("depth projection failed to commute")
                targets |= 1 << pair_index((evolved.left[-1], evolved.right[0]))
        rows.append(targets)
    matrix = BooleanPairMatrix(tuple(rows))
    if matrix.maximum_successors > 4:
        raise AssertionError("the local radius-one stencil needs >4 responses")
    return matrix


@dataclass(frozen=True, slots=True)
class ConditionalDepthReturn:
    """Stroboscopic matrix for a declared periodic outer inlet program."""

    physical_period: int
    action: BooleanPairMatrix
    phase_matrices: tuple[BooleanPairMatrix, ...]
    source_period_certified: bool = False

    def __post_init__(self) -> None:
        if self.source_period_certified:
            raise ValueError(
                "a finite boundary word cannot certify infinite periodicity"
            )
        if self.physical_period != 2 * len(self.phase_matrices):
            raise ValueError("incorrect stroboscopic physical clock")

    def pointed_returns(
        self, initial_pair: tuple[int, int], periods: int = 1
    ) -> tuple[tuple[int, int], ...]:
        return self.action.power(periods).endpoints(initial_pair)


def conditional_depth_return(
    outer: tuple[BirthRingState, ...],
) -> ConditionalDepthReturn:
    """Build an exact matrix for one supplied closed outer word."""
    if (
        type(outer) is not tuple
        or len(outer) < 2
        or not all(type(state) is BirthRingState for state in outer)
        or outer[-1] != outer[0]
    ):
        raise ValueError("closed periodic outer program required")
    matrices = tuple(
        outer_step_matrix(first, second) for first, second in pairwise(outer)
    )
    action = BooleanPairMatrix.identity()
    for matrix in matrices:
        action = action.then(matrix)
    return ConditionalDepthReturn(2 * len(matrices), action, matrices)


@dataclass(frozen=True, slots=True)
class SourceConditionedDepthReturn:
    """Finite deterministic transfer conditioned on one complete initial halo."""

    physical_duration: int
    source_halo_pairs: int
    action: BooleanPairMatrix
    pointed_trace: tuple[tuple[int, int], ...]
    infinite_period_certified: bool = False

    def __post_init__(self) -> None:
        if self.infinite_period_certified:
            raise ValueError("a finite causal halo cannot certify infinite repetition")
        if self.physical_duration != 2 * (len(self.pointed_trace) - 1):
            raise ValueError("correlated trace must have one entry per F step")
        if self.action.maximum_successors > 1:
            raise ValueError("fixed-halo action must be deterministic")

    def pointed_endpoint(self, initial_pair: tuple[int, int]) -> tuple[int, int] | None:
        image = self.action.endpoints(initial_pair)
        return image[0] if image else None


def source_conditioned_depth_return(
    outer: tuple[BirthRingState, ...],
    source_halo: BirthRingState,
    initial_pair: tuple[int, int],
    *,
    odd_outer: tuple[tuple[tuple[int, int], ...], ...] | None = None,
) -> SourceConditionedDepthReturn:
    """Propagate one initial halo and filter rows by its finite source trace.

    The caller must obtain ``outer`` and ``source_halo`` from the same live
    source owner. The finite algorithm verifies that the halo contains at
    least K+1+m pairs; outside digits then cannot enter the requested K+1
    output during ``m`` F ticks. Candidate pairs vary once at the initial
    seam, while all deeper halo digits remain jointly fixed.
    """
    if (
        type(source_halo) is not BirthRingState
        or type(outer) is not tuple
        or len(outer) < 2
        or not all(type(state) is BirthRingState for state in outer)
    ):
        raise ValueError("source-conditioned action needs a finite outer word")
    pairs = outer[0].pairs
    steps = len(outer) - 1
    if (
        source_halo.pairs < pairs + 1 + steps
        or ring_outer(source_halo, pairs) != outer[0]
        or any(
            state.pairs != pairs or state.phase != (outer[0].phase + 2 * j) % 4
            for j, state in enumerate(outer)
        )
        or ring_next_pair(source_halo, pairs) != initial_pair
    ):
        raise ValueError("incomplete or inconsistent initial causal halo")
    if odd_outer is not None and (
        type(odd_outer) is not tuple
        or len(odd_outer) != steps
        or any(
            type(row) is not tuple
            or len(row) != pairs
            or any(
                type(pair) is not tuple
                or len(pair) != 2
                or any(type(digit) is not int or not 0 <= digit <= 9 for digit in pair)
                for pair in row
            )
            for row in odd_outer
        )
    ):
        raise ValueError("odd-generation outer guard has incorrect length")

    pair_index(initial_pair)
    halo_size = source_halo.pairs
    rows: list[int] = []
    pointed_trace: tuple[tuple[int, int], ...] = ()
    for initial in ALL_PAIRS:
        left = list(source_halo.left)
        right = list(source_halo.right)
        left[pairs], right[halo_size - pairs - 1] = initial
        current_halo = CertifiedHalo(
            BirthRingState(tuple(left), tuple(right), source_halo.phase), halo_size
        )
        trace: list[tuple[int, int]] = []
        admitted = True
        for tick in range(steps):
            current = current_halo.outer(pairs + 1)
            if ring_outer(current, pairs) != outer[tick]:
                admitted = False
                break
            next_pair = ring_next_pair(current, pairs)
            trace.append(next_pair)
            if (
                odd_outer is not None
                and odd_boundary_pairs(outer[tick], BirthRingPorts(*next_pair))
                != odd_outer[tick]
            ):
                admitted = False
                break
            current_halo = current_halo.step()
        final_outer = current_halo.outer(pairs + 1)
        if admitted and ring_outer(final_outer, pairs) == outer[-1]:
            trace.append(ring_next_pair(final_outer, pairs))
            rows.append(1 << pair_index(trace[-1]))
            if initial == initial_pair:
                pointed_trace = tuple(trace)
        else:
            rows.append(0)
    if not pointed_trace:
        raise AssertionError("pointed source path contradicts its supplied halo")
    return SourceConditionedDepthReturn(
        2 * steps, halo_size, BooleanPairMatrix(tuple(rows)), pointed_trace
    )


def rooted_finite_depth_trace(
    source_halo: BirthRingState, *, outer_pairs: int, f_steps: int
) -> tuple[tuple[BirthRingState, ...], tuple[tuple[tuple[int, int], ...] | None, ...]]:
    """Propagate one fixed halo and return K+1 outer and odd output words."""
    if (
        type(outer_pairs) is not int
        or outer_pairs < 1
        or type(f_steps) is not int
        or f_steps < 0
        or type(source_halo) is not BirthRingState
        or source_halo.pairs < outer_pairs + 1 + f_steps
    ):
        raise ValueError("rooted finite period needs K+1+duration initial halo pairs")
    current_halo = CertifiedHalo(source_halo, source_halo.pairs)
    states: list[BirthRingState] = []
    odd: list[tuple[tuple[int, int], ...] | None] = []
    for tick in range(f_steps + 1):
        if tick == f_steps:
            states.append(current_halo.outer(outer_pairs + 1))
            break
        outer, odd_row = halo_outer_odd_row(current_halo, outer_pairs)
        states.append(outer)
        odd.append(odd_row)
        current_halo = current_halo.step()
    return tuple(states), tuple(odd)


@dataclass(frozen=True, slots=True)
class SourceConditionedDepthWindow(SourceAuthorizedRecord):
    """Finite 2rev10 depth relation bound to an existing prepared source."""

    physical_prefix: int
    source_root: int
    source_phase: int
    source_horizon: int
    start_f_steps: int
    outer_pairs: int
    f_steps: int
    source_halo: BirthRingState
    initial_pair: tuple[int, int]
    outer_trace: tuple[BirthRingState, ...]
    odd_outer: tuple[tuple[tuple[int, int], ...], ...]
    transfer: SourceConditionedDepthReturn

    @property
    def physical_duration(self) -> int:
        self.validate_source_authority()
        return 2 * self.f_steps

    @property
    def start_generation(self) -> int:
        self.validate_source_authority()
        return self.physical_prefix + 2 * self.start_f_steps

    @property
    def end_generation(self) -> int:
        self.validate_source_authority()
        return self.physical_prefix + 2 * (self.start_f_steps + self.f_steps)

    @property
    def action(self) -> BooleanPairMatrix:
        self.validate_source_authority()
        return self.transfer.action

    def validate_source_authority(self) -> SourceRecordAuthority:
        authority = validate_source_record(self)
        if (
            authority.root != self.source_root
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
            or self.start_f_steps + self.f_steps > self.source_horizon
            or type(self.source_halo) is not BirthRingState
            or self.source_halo.phase
            != (self.source_phase + 2 * self.start_f_steps) % 4
            or self.source_halo.pairs != self.outer_pairs + 1 + self.f_steps
            or self.initial_pair != ring_next_pair(self.source_halo, self.outer_pairs)
            or self.transfer.physical_duration != 2 * self.f_steps
            or self.transfer.source_halo_pairs != self.source_halo.pairs
            or self.transfer.infinite_period_certified
            or len(self.outer_trace) != self.f_steps + 1
            or len(self.odd_outer) != self.f_steps
        ):
            raise ValueError("invalid source-conditioned depth window authority")
        return authority

    def to_packet(self) -> dict[str, object]:
        """Serialize only after revalidating the live source-root authority."""
        self.validate_source_authority()
        start_generation = self.physical_prefix + 2 * self.start_f_steps
        return {
            "status": "available",
            "mode": "source_conditioned_finite_halo",
            "relation_semantics": "exact_fixed_halo_finite_relation",
            "source_root_assignment_joined": True,
            "physical_prefix_generation": self.physical_prefix,
            "source_horizon_f_steps": self.source_horizon,
            "start_generation": start_generation,
            "end_generation": start_generation + 2 * self.f_steps,
            "outer_pairs": self.outer_pairs,
            "f_steps": self.f_steps,
            "physical_duration": 2 * self.f_steps,
            "source_halo_pairs": self.source_halo.pairs,
            "initial_pair": list(self.initial_pair),
            "outer_trace": [
                {
                    "phase": state.phase,
                    "left": list(state.left),
                    "right": list(state.right),
                }
                for state in self.outer_trace
            ],
            "odd_outer": [[list(pair) for pair in row] for row in self.odd_outer],
            "pointed_trace": [list(pair) for pair in self.transfer.pointed_trace],
            "transition_rows": list(self.transfer.action.rows),
            "infinite_period_certified": False,
        }


def source_conditioned_depth_window(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int = 0,
    f_steps: int | None = None,
) -> SourceConditionedDepthWindow:
    """Return a bounded causal-halo action from an already prepared source.

    At most four T-squared ticks are admitted. The requested initial halo is
    sampled directly from the existing source root through shared pointed
    windows; this does not issue a future source or assume repetition. The
    ledger reservation covers construction scratch only; the returned action
    is caller-retained Python data, not a ledger-retained cache entry. Use
    :func:`source_conditioned_depth_window_packet` to publish its packet while
    the same reservation covers construction and serialization.
    """
    return _build_source_conditioned_depth_window(
        source,
        outer_pairs=outer_pairs,
        start_f_steps=start_f_steps,
        f_steps=f_steps,
    )


def source_conditioned_depth_window_packet(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int = 0,
    f_steps: int | None = None,
) -> dict[str, object]:
    """Build and serialize a finite matrix under one bounded reservation.

    The explicit matrix demand also replays this same finite source interval
    as shrinking, source-refilled halo blocks. No horizon beyond the requested
    matrix is sampled.
    """

    def publish(window: SourceConditionedDepthWindow) -> dict[str, object]:
        continued = build_source_continued_halo_trace(
            source,
            outer_pairs=window.outer_pairs,
            start_f_steps=window.start_f_steps,
            f_steps=window.f_steps,
            block_f_steps=min(2, window.f_steps),
        )
        if (
            tuple(
                ring_outer(state, window.outer_pairs) for state in continued.even_outer
            )
            != window.outer_trace
            or tuple(
                ring_next_pair(state, window.outer_pairs)
                for state in continued.even_outer
            )
            != window.transfer.pointed_trace
        ):
            raise AssertionError("refilled halo diverged from the matrix source trace")
        if any(
            row is None or row[: window.outer_pairs] != expected
            for row, expected in zip(continued.odd_outer, window.odd_outer, strict=True)
        ):
            raise AssertionError("refilled odd halo diverged from the matrix trace")
        packet = window.to_packet()
        packet["source_backed_continuation"] = continued.to_packet()
        return packet

    return _build_source_conditioned_depth_window(
        source,
        outer_pairs=outer_pairs,
        start_f_steps=start_f_steps,
        f_steps=f_steps,
        publish=publish,
    )


@overload
def _build_source_conditioned_depth_window(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int | None,
    publish: None = None,
) -> SourceConditionedDepthWindow: ...


@overload
def _build_source_conditioned_depth_window(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int | None,
    publish: Callable[[SourceConditionedDepthWindow], _Published],
) -> _Published: ...


def _build_source_conditioned_depth_window(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int | None,
    publish: Callable[[SourceConditionedDepthWindow], _Published] | None = None,
) -> SourceConditionedDepthWindow | _Published:
    """Build an issued window and optionally publish it before release."""
    from .source_bound_bank import PointedBankSource as BankSource

    if type(source) is not BankSource:
        raise TypeError("depth matrix needs an existing PointedBankSource")
    source.validate(require_issued_cursor=source.f_steps > 0)
    if (
        type(outer_pairs) is not int
        or outer_pairs < 1
        or type(start_f_steps) is not int
        or start_f_steps < 0
        or start_f_steps >= source.f_steps
    ):
        raise SourceConditionedDepthWindowUnavailable(
            "depth matrix lies outside its prepared source"
        )
    if f_steps is None:
        f_steps = min(4, source.f_steps - start_f_steps)
    if (
        type(f_steps) is not int
        or not 1 <= f_steps <= 4
        or start_f_steps + f_steps > source.f_steps
    ):
        raise SourceConditionedDepthWindowUnavailable(
            "depth matrix horizon must be 1..4 prepared F steps"
        )
    halo_pairs = outer_pairs + 1 + f_steps
    if halo_pairs > 18:
        raise SourceConditionedDepthWindowUnavailable(
            "source-conditioned causal halo exceeds 18 pairs"
        )
    start_width = source.width_in + sum(growth_ports(source.phase, start_f_steps))
    if 2 * halo_pairs > start_width:
        raise SourceConditionedDepthWindowUnavailable(
            "prepared source is too narrow for the full causal halo"
        )
    left = source.engine.pointed_window(
        source.root, start_f_steps, source.phase, 0, halo_pairs
    )
    right = source.engine.pointed_window(
        source.root,
        start_f_steps,
        source.phase,
        start_width - halo_pairs,
        halo_pairs,
    )
    phase = (source.phase + 2 * start_f_steps) % 4
    halo = BirthRingState(left, right, phase)
    initial_pair = ring_next_pair(halo, outer_pairs)
    # Bound the finite matrix, trace, and source-record construction against
    # the same owner as the already prepared source. The two pointed windows
    # above are separately charged by Hashlife itself.
    with source.ledger.reservation(source.scratch_owner, entries=1024, nodes=1024):
        rooted_states, rooted_odd = rooted_finite_depth_trace(
            halo, outer_pairs=outer_pairs, f_steps=f_steps
        )
        outer = tuple(ring_outer(state, outer_pairs) for state in rooted_states)
        odd_rows: list[tuple[tuple[int, int], ...]] = []
        for row in rooted_odd:
            if row is None:
                raise AssertionError("finite rooted trace omitted an odd row")
            odd_rows.append(row[:outer_pairs])
        odd_outer = tuple(odd_rows)
        transfer = source_conditioned_depth_return(
            outer, halo, initial_pair, odd_outer=odd_outer
        )
        record = SourceConditionedDepthWindow(
            source.physical_prefix,
            source.root,
            source.phase,
            source.f_steps,
            start_f_steps,
            outer_pairs,
            f_steps,
            halo,
            initial_pair,
            outer,
            odd_outer,
            transfer,
        )
        issued = issue_source_record(
            record,
            source.arena,
            source.root,
            source_generation=source.physical_prefix,
        )
        issued.validate_source_authority()
        if publish is not None:
            return publish(issued)
    return issued


__all__ = [
    "ALL_PAIRS",
    "BooleanPairMatrix",
    "CertifiedHalo",
    "ConditionalDepthReturn",
    "SourceConditionedDepthReturn",
    "SourceConditionedDepthWindow",
    "SourceConditionedDepthWindowUnavailable",
    "SourceContinuedHaloTrace",
    "conditional_depth_return",
    "outer_step_matrix",
    "pair_index",
    "rooted_finite_depth_trace",
    "source_conditioned_depth_return",
    "source_conditioned_depth_window",
    "source_conditioned_depth_window_packet",
    "source_continued_halo_trace_packet_from_source",
]
