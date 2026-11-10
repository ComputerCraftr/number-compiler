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

from number_compiler.arithmetic.automata.slp_walks import symbol_at
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
from .stencil_moore import stencil_cell
from .temporal_birth_ring import BirthRingPorts, BirthRingState, odd_boundary_pairs
from .temporal_certified_halo import (
    CertifiedHalo,
    SourceConditionedDepthWindowUnavailable,
    SourceContinuedHaloTrace,
    halo_outer_odd_row,
    ring_next_pair,
    ring_outer,
    source_continued_halo_trace_packet_from_source,
)
from .temporal_hashlife import growth_ports
from .temporal_issued_root_path import (
    SourceIssuedRootPath,
    source_issued_root_path,
)

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


def outer_port_class(current: BirthRingState, left: int, right: int) -> tuple[int, int]:
    """Return the two exact Boolean inlet observations of an outer F-step.

    The left inlet is a right-neighbour of the left strip's last stencil cell,
    so that cell observes the carry bit after doubling the inlet with the
    current boundary's incoming carry. The right inlet is a left-neighbour of
    the right strip's first stencil cell, so it observes its threshold bit.
    A birth punctures the corresponding inlet from the outer ring.
    """
    if type(current) is not BirthRingState:
        raise TypeError("outer port classes require a BirthRingState")
    if any(type(digit) is not int or not 0 <= digit <= 9 for digit in (left, right)):
        raise ValueError("outer inlet ports must be decimal digits")
    birth_left, birth_right = growth_ports(current.phase, 1)
    left_response = (
        0 if birth_left else int((2 * left + int(current.left[-1] >= 5)) % 10 >= 5)
    )
    right_response = 0 if birth_right else int(right >= 5)
    return left_response, right_response


def admitted_outer_port_classes(
    current: BirthRingState, following: BirthRingState
) -> frozenset[tuple[int, int]]:
    """Compute accepted inlet classes with at most four ring advances.

    This is only a necessary outer-successor test for a source-conditioned
    halo. The halo, odd-generation guards and pointed source path remain
    independently checked by their existing owners.
    """
    if (
        type(current) is not BirthRingState
        or type(following) is not BirthRingState
        or current.pairs != following.pairs
        or following.phase != (current.phase + 2) % 4
    ):
        raise ValueError("outer step requires compatible moving-boundary rings")
    birth_left, birth_right = growth_ports(current.phase, 1)
    left_classes = (0,) if birth_left else (0, 1)
    right_classes = (0,) if birth_right else (0, 1)
    accepted: set[tuple[int, int]] = set()
    for left_response in left_classes:
        for right_response in right_classes:
            representative = BirthRingPorts(
                3 if left_response else 0,
                5 if right_response else 0,
            )
            if current.advance(representative)[0] == following:
                accepted.add((left_response, right_response))
    return frozenset(accepted)


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
    """Eliminate all next-depth inlet digits for one exact outer F-step.

    The outer ring only observes two Boolean responses from an inlet pair:
    the left cell's outgoing high bit and the right cell's high bit.  Quotient
    inlet pairs by those guards before checking the supplied outer successor.
    Once a guard class is admitted, compute only the two pointed stencil cells
    for each of the four inward guard ports; the full ring successor is not
    rebuilt for every pair.
    """
    if (
        type(current) is not BirthRingState
        or type(following) is not BirthRingState
        or current.pairs != following.pairs
        or following.phase != (current.phase + 2) % 4
    ):
        raise ValueError("outer step requires compatible moving-boundary rings")
    birth_left, birth_right = growth_ports(current.phase, 1)
    accepted = admitted_outer_port_classes(current, following)
    row_guards = tuple(
        outer_port_class(current, left, right) for left, right in ALL_PAIRS
    )

    pair_count = current.pairs

    def extended_left(index: int, candidate: int, inward: int) -> int:
        if index < 0:
            return 0
        if index < pair_count:
            return current.left[index]
        if index == pair_count:
            return candidate
        if index == pair_count + 1:
            return inward
        raise AssertionError("upper pointed stencil escaped its one-cell halo")

    def extended_right(index: int, candidate: int, inward: int) -> int:
        if index == -1:
            return inward
        if index == 0:
            return candidate
        if 1 <= index <= pair_count:
            return current.right[index - 1]
        if index == pair_count + 1:
            return 0
        raise AssertionError("lower pointed stencil escaped its one-cell halo")

    left_center = pair_count - birth_left
    right_center = birth_right
    rows: list[int] = []
    for (left, right), guard in zip(ALL_PAIRS, row_guards, strict=True):
        if guard not in accepted:
            rows.append(0)
            continue
        targets = 0
        for inward_left in (0, 3):
            left_output = stencil_cell(
                extended_left(left_center - 1, left, inward_left),
                extended_left(left_center, left, inward_left),
                extended_left(left_center + 1, left, inward_left),
            )
            for inward_right in (0, 5):
                right_output = stencil_cell(
                    extended_right(right_center - 1, right, inward_right),
                    extended_right(right_center, right, inward_right),
                    extended_right(right_center + 1, right, inward_right),
                )
                targets |= 1 << pair_index((left_output, right_output))
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
    seam, while all deeper halo digits remain jointly fixed. The exact
    outer-port quotient rejects impossible rows before copying the halo and
    before each subsequent halo advance; it does not replace the full-halo,
    odd-generation, or pointed-source checks.
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
    # Compute the exact outer-successor guard quotient before allocating any
    # candidate halo copies. This only removes candidates that cannot match
    # the supplied outer trace; survivors still undergo the full halo and
    # odd-generation checks below.
    admitted_classes = tuple(
        admitted_outer_port_classes(outer[tick], outer[tick + 1])
        for tick in range(steps)
    )
    rows: list[int] = []
    pointed_trace: tuple[tuple[int, int], ...] = ()
    for initial in ALL_PAIRS:
        if outer_port_class(outer[0], *initial) not in admitted_classes[0]:
            rows.append(0)
            continue
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
            if outer_port_class(outer[tick], *next_pair) not in admitted_classes[tick]:
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
    issued_path: SourceIssuedRootPath | None = None,
) -> SourceConditionedDepthWindow:
    """Return a bounded causal-halo action from an already prepared source.

    At most four T-squared ticks are admitted. The requested initial halo is
    sampled from an already prepared source root, either through pointed
    windows or an authenticated adjacent-root path. This does not issue a
    future source or assume repetition. The ledger reservation covers
    construction scratch only; the returned action is caller-retained Python
    data, not a ledger-retained cache entry. Use
    :func:`source_conditioned_depth_window_packet` to publish its packet while
    the same reservation covers construction and serialization.
    """
    return _build_source_conditioned_depth_window(
        source,
        outer_pairs=outer_pairs,
        start_f_steps=start_f_steps,
        f_steps=f_steps,
        issued_path=issued_path,
    )


def source_conditioned_depth_window_packet(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int = 0,
    f_steps: int | None = None,
) -> dict[str, object]:
    """Build and serialize a finite matrix under one bounded reservation.

    Its continuation packet is projected from the same single source-issued
    causal halo as the matrix. No source-refill traversal is repeated.
    """

    def publish(
        window: SourceConditionedDepthWindow,
        even_trace: tuple[BirthRingState, ...],
        odd_trace: tuple[tuple[tuple[int, int], ...] | None, ...],
    ) -> dict[str, object]:
        """Publish two checked projections of the already-built source trace."""
        if (
            tuple(ring_outer(state, window.outer_pairs) for state in even_trace)
            != window.outer_trace
            or tuple(ring_next_pair(state, window.outer_pairs) for state in even_trace)
            != window.transfer.pointed_trace
        ):
            raise AssertionError("shared halo diverged from the matrix source trace")
        if any(
            row is None or row[: window.outer_pairs] != expected
            for row, expected in zip(odd_trace, window.odd_outer, strict=True)
        ):
            raise AssertionError("shared odd halo diverged from the matrix trace")
        continued = SourceContinuedHaloTrace(
            window.physical_prefix,
            window.source_root,
            window.source_phase,
            window.source_horizon,
            window.start_f_steps,
            window.outer_pairs,
            window.f_steps,
            window.f_steps,
            even_trace,
            odd_trace,
            (),
            window.outer_pairs + 1,
            window.outer_pairs + 1 + window.f_steps,
        )
        issued_continued = issue_source_record(
            continued,
            source.arena,
            source.root,
            source_generation=source.physical_prefix,
        )
        packet = window.to_packet()
        packet["source_backed_continuation"] = issued_continued.to_packet()
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
    issued_path: SourceIssuedRootPath | None = None,
    publish: None = None,
) -> SourceConditionedDepthWindow: ...


@overload
def _build_source_conditioned_depth_window(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int | None,
    issued_path: SourceIssuedRootPath | None = None,
    publish: Callable[
        [
            SourceConditionedDepthWindow,
            tuple[BirthRingState, ...],
            tuple[tuple[tuple[int, int], ...] | None, ...],
        ],
        _Published,
    ],
) -> _Published: ...


def _build_source_conditioned_depth_window(
    source: PointedBankSource,
    *,
    outer_pairs: int,
    start_f_steps: int,
    f_steps: int | None,
    issued_path: SourceIssuedRootPath | None = None,
    publish: Callable[
        [
            SourceConditionedDepthWindow,
            tuple[BirthRingState, ...],
            tuple[tuple[tuple[int, int], ...] | None, ...],
        ],
        _Published,
    ]
    | None = None,
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
    path_start: int | None = None
    if issued_path is None:
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
        path_root: int | None = None
    else:
        if type(issued_path) is not SourceIssuedRootPath:
            raise TypeError("depth puncture needs an issued root path")
        issued_path.validate_for_source(source)
        path_start = start_f_steps - issued_path.root_offset
        if path_start < 0 or path_start + f_steps >= len(issued_path.roots):
            raise SourceConditionedDepthWindowUnavailable(
                "issued root path does not cover the requested window"
            )
        path_root = issued_path.roots[path_start]
        if source.arena.nodes[path_root].length != start_width:
            raise ArithmeticError("issued root and temporal growth disagree")
        left = tuple(
            symbol_at(source.arena, path_root, index) for index in range(halo_pairs)
        )
        right = tuple(
            symbol_at(source.arena, path_root, start_width - halo_pairs + index)
            for index in range(halo_pairs)
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
        if issued_path is not None:
            if path_start is None:
                raise AssertionError("issued root path start was not resolved")
            retained = outer_pairs + 1
            for offset, predicted in enumerate(rooted_states):
                root = issued_path.roots[path_start + offset]
                width = source.arena.nodes[root].length
                expected_width = source.width_in + sum(
                    growth_ports(source.phase, start_f_steps + offset)
                )
                if width != expected_width:
                    raise ArithmeticError("issued depth root has incorrect birth width")
                actual = BirthRingState(
                    tuple(
                        symbol_at(source.arena, root, index)
                        for index in range(retained)
                    ),
                    tuple(
                        symbol_at(source.arena, root, width - retained + index)
                        for index in range(retained)
                    ),
                    (source.phase + 2 * (start_f_steps + offset)) % 4,
                )
                if actual != predicted:
                    raise ArithmeticError(
                        "source-issued depth root violates the complete port halo"
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
            return publish(issued, rooted_states, rooted_odd)
    return issued


__all__ = [
    "ALL_PAIRS",
    "BooleanPairMatrix",
    "CertifiedHalo",
    "ConditionalDepthReturn",
    "SourceConditionedDepthReturn",
    "SourceConditionedDepthWindow",
    "SourceIssuedRootPath",
    "SourceConditionedDepthWindowUnavailable",
    "SourceContinuedHaloTrace",
    "admitted_outer_port_classes",
    "conditional_depth_return",
    "outer_port_class",
    "outer_step_matrix",
    "pair_index",
    "rooted_finite_depth_trace",
    "source_conditioned_depth_return",
    "source_conditioned_depth_window",
    "source_issued_root_path",
    "source_conditioned_depth_window_packet",
    "source_continued_halo_trace_packet_from_source",
]
