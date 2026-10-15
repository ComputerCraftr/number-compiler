"""Guarded XOR edits and exact spatial folds of supplied binary SLPs.

The source is an exact caller-supplied word.  Admission snapshots its reachable
SLP once; it does not infer a power-of-three label from the word, a clock, or
any local observation.  Signed Fermat folds, tripling, and radial width are
source observations only and do not decide primality.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import pairwise

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_interval
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.power_numbers.fermat_binary_pair_fold import (
    MAX_BINARY_SLP_NODES,
    FermatBinaryFoldAction,
    FermatBinarySLPSnapshot,
)
from number_compiler.sequences.power_numbers.fermat_signed_reducer import (
    MAX_FERMAT_FOLD_WIDTH,
    fold_signed_fermat,
)

MAX_XOR_RUNS = 4_096
MAX_XOR_WORK = 1_000_000
MAX_RADIAL_WORK = 1_000_000


@dataclass(frozen=True, slots=True)
class GuardedXorRun:
    """One uniform guarded interval toggle in the admitted source word.

    ``pivot_label`` is an occurrence coordinate supplied by the caller.  It is
    descriptive metadata only; it does not certify a power or source identity.
    """

    start: int
    length: int
    expected_bit: int
    pivot_label: int | None = None

    def __post_init__(self) -> None:
        require_integer(self.start, "run start", 0)
        require_integer(self.length, "run length", 1)
        require_integer(self.expected_bit, "run expected bit", 0, 1)
        if self.pivot_label is not None:
            require_integer(self.pivot_label, "pivot label", 0)
            if self.pivot_label.bit_length() > 4_096:
                raise ValueError("pivot label exceeds source-coordinate budget")
        if (self.start + self.length).bit_length() > 4_096:
            raise ValueError("XOR run endpoint exceeds source-coordinate budget")

    @property
    def end(self) -> int:
        return self.start + self.length


@dataclass(frozen=True, slots=True)
class RadialWidthObservation:
    """Exact one-step bit-width change for tripling this complete source word."""

    source_bits: int
    threshold_comparison: int
    tripled_bits: int

    def __post_init__(self) -> None:
        require_integer(self.source_bits, "radial source width", 1)
        if type(
            self.threshold_comparison
        ) is not int or self.threshold_comparison not in (-1, 0, 1):
            raise ValueError(self.threshold_comparison)
        expected = self.source_bits + (2 if self.threshold_comparison >= 0 else 1)
        require_integer(self.tripled_bits, "tripled source width", expected, expected)
        if self.tripled_bits != expected:
            raise ValueError(
                "radial width does not match its exact threshold comparison"
            )


@dataclass(frozen=True, slots=True)
class FermatTripleFoldObservation:
    """Fermat residue of three times a source, not a concatenable word action."""

    width: int
    source_length: int
    residue: int

    def __post_init__(self) -> None:
        width = require_integer(
            self.width, "Fermat fold width", 1, MAX_FERMAT_FOLD_WIDTH
        )
        require_integer(self.source_length, "source length", 0)
        require_integer(self.residue, "triple-fold residue", 0, 1 << width)


@dataclass(frozen=True, slots=True)
class _PeriodicCompare:
    """First mismatch against the alternating word 1010... in either phase."""

    length: int
    first: tuple[tuple[int, int] | None, tuple[int, int] | None]

    @classmethod
    def identity(cls) -> _PeriodicCompare:
        return cls(0, (None, None))

    def then(self, following: _PeriodicCompare) -> _PeriodicCompare:
        result: list[tuple[int, int] | None] = []
        for phase in (0, 1):
            mismatch = self.first[phase]
            if mismatch is not None:
                result.append(mismatch)
                continue
            suffix = following.first[(phase + self.length) & 1]
            result.append(
                None if suffix is None else (self.length + suffix[0], suffix[1])
            )
        return _PeriodicCompare(self.length + following.length, (result[0], result[1]))

    def repeat(self, count: int) -> _PeriodicCompare:
        if type(count) is not int or count < 0:
            raise ValueError(("comparison-repeat-count", count))
        if count == 0:
            return self.identity()
        result: list[tuple[int, int] | None] = []
        for phase in (0, 1):
            mismatch = self.first[phase]
            if mismatch is None and self.length & 1 and count >= 2:
                suffix = self.first[phase ^ 1]
                if suffix is not None:
                    mismatch = (self.length + suffix[0], suffix[1])
            result.append(mismatch)
        return _PeriodicCompare(self.length * count, (result[0], result[1]))


def _terminal_compare(bit: int, flip: int) -> _PeriodicCompare:
    actual = bit ^ flip
    first = tuple(
        (0, 1 if actual > (1 - phase) else -1) if actual != (1 - phase) else None
        for phase in (0, 1)
    )
    return _PeriodicCompare(1, (first[0], first[1]))


def _fold_two_adic_periodic_interval(
    snapshot: FermatBinarySLPSnapshot,
    begin: int,
    end: int,
    *,
    source_flip: int,
    summaries: list[
        tuple[
            tuple[_PeriodicCompare, _PeriodicCompare],
            tuple[_PeriodicCompare, _PeriodicCompare],
        ]
    ],
    max_visits: int,
    total_visits: list[int],
) -> _PeriodicCompare:
    def visit() -> None:
        total_visits[0] += 1
        if total_visits[0] > max_visits:
            raise ValueError(("radial-source-work-budget", max_visits))

    return fold_slp_interval(
        snapshot,
        snapshot.root,
        begin,
        end,
        identity=_PeriodicCompare.identity(),
        length=lambda node_id: snapshot.nodes[node_id].length,
        full_value=lambda node_id, reverse: summaries[node_id][int(reverse)][
            source_flip
        ],
        compose=lambda lower, higher: lower.then(higher),
        repeat=lambda block, count: block.repeat(count),
        reverse=True,
        on_visit=visit,
    )


def _edit_segments(
    begin: int,
    end: int,
    runs: tuple[GuardedXorRun, ...],
    *,
    msb_coordinates: bool,
    source_length: int,
) -> tuple[tuple[int, int, int], ...]:
    events: dict[int, int] = {}
    for run in runs:
        if msb_coordinates:
            run_start = source_length - run.end
            run_end = source_length - run.start
        else:
            run_start = run.start
            run_end = run.end
        left = max(begin, run_start)
        right = min(end, run_end)
        if left < right:
            events[left] = events.get(left, 0) + 1
            events[right] = events.get(right, 0) + 1
    points = sorted({begin, end, *events})
    segments: list[tuple[int, int, int]] = []
    flip = 0
    for left, right in pairwise(points):
        flip ^= events.get(left, 0) & 1
        if left < right:
            segments.append((left, right, flip))
    return tuple(segments)


@dataclass(frozen=True, slots=True, init=False)
class GuardedBinarySource:
    """Owned snapshot of a caller's binary SLP plus authenticated run edits."""

    _owner: SLPArena
    _raw_root: int
    _snapshot: FermatBinarySLPSnapshot
    _runs: tuple[GuardedXorRun, ...]
    _work_used: int

    @classmethod
    def admit(
        cls,
        arena: SLPArena,
        root: int,
        *,
        max_nodes: int = MAX_BINARY_SLP_NODES,
    ) -> GuardedBinarySource:
        snapshot = FermatBinarySLPSnapshot.admit(arena, root, max_nodes=max_nodes)
        source = object.__new__(cls)
        object.__setattr__(source, "_owner", arena)
        object.__setattr__(source, "_raw_root", root)
        object.__setattr__(source, "_snapshot", snapshot)
        object.__setattr__(source, "_runs", ())
        object.__setattr__(source, "_work_used", len(snapshot.nodes))
        return source

    @property
    def source_length(self) -> int:
        return self._snapshot.nodes[self._snapshot.root].length

    @property
    def edits(self) -> tuple[GuardedXorRun, ...]:
        return self._runs

    @property
    def admitted_node_count(self) -> int:
        return len(self._snapshot.nodes)

    def require_binding(self, arena: SLPArena, root: int) -> None:
        """Reject a foreign arena or root when crossing an adapter boundary."""
        if arena is not self._owner or type(root) is not int or root != self._raw_root:
            raise ValueError("binary source handle is bound to another arena/root")

    def _count_current_interval(
        self,
        begin: int,
        end: int,
        *,
        work_limit: int,
    ) -> tuple[int, int]:
        total_ones = 0
        visits = 0
        for left, right, flipped in _edit_segments(
            begin,
            end,
            self._runs,
            msb_coordinates=False,
            source_length=self.source_length,
        ):
            remaining = work_limit - visits
            if remaining < 1:
                raise ValueError(("xor-guard-work-budget", work_limit))
            base_ones, segment_visits = self._snapshot.count_ones(
                left,
                right,
                max_visits=min(MAX_BINARY_SLP_NODES, remaining),
            )
            visits += segment_visits
            if visits > work_limit:
                raise ValueError(("xor-guard-work-budget", work_limit))
            segment_length = right - left
            total_ones += segment_length - base_ones if flipped else base_ones
        return total_ones, visits

    def toggle_run(
        self,
        start: int,
        length: int,
        expected_bit: int,
        *,
        pivot_label: int | None = None,
        work_budget: int = MAX_XOR_WORK,
    ) -> GuardedBinarySource:
        """Toggle a currently uniform source interval after checking its guard."""
        work_budget = require_integer(work_budget, "xor work budget", 1, MAX_XOR_WORK)
        remaining_total = MAX_XOR_WORK - self._work_used
        effective_budget = min(work_budget, remaining_total)
        if effective_budget < 1:
            raise ValueError(("xor-source-total-work-budget", MAX_XOR_WORK))
        run = GuardedXorRun(start, length, expected_bit, pivot_label)
        if run.end > self.source_length:
            raise ValueError(("xor-run-outside-source", run.end, self.source_length))
        if len(self._runs) >= MAX_XOR_RUNS:
            raise ValueError(("xor-run-count-budget", MAX_XOR_RUNS))
        run_count = len(self._runs)
        scan_work = (run_count + 1) * (run_count.bit_length() + 4)
        if scan_work >= effective_budget:
            raise ValueError(("xor-guard-work-budget", effective_budget))
        ones, visits = self._count_current_interval(
            run.start,
            run.end,
            work_limit=effective_budget - scan_work,
        )
        if ones != (run.length if run.expected_bit else 0):
            raise ValueError("XOR run source guard does not match the current word")
        used = scan_work + visits
        if used > effective_budget or self._work_used + used > MAX_XOR_WORK:
            raise ValueError(("xor-source-total-work-budget", MAX_XOR_WORK))
        updated = object.__new__(type(self))
        object.__setattr__(updated, "_owner", self._owner)
        object.__setattr__(updated, "_raw_root", self._raw_root)
        object.__setattr__(updated, "_snapshot", self._snapshot)
        object.__setattr__(updated, "_runs", self._runs + (run,))
        object.__setattr__(updated, "_work_used", self._work_used + used)
        return updated

    def fold(
        self, width: int, *, max_nodes: int = MAX_BINARY_SLP_NODES
    ) -> FermatBinaryFoldAction:
        """Return the complete edited word's exact Fermat spatial residue."""
        width = require_integer(width, "Fermat fold width", 1, MAX_FERMAT_FOLD_WIDTH)
        base = self._snapshot.fold(width=width, max_nodes=max_nodes)
        correction = 0
        for run in self._runs:
            sign = 1 if run.expected_bit == 0 else -1
            correction += sign * (
                self._signed_two_power_mod(run.end, width)
                - self._signed_two_power_mod(run.start, width)
            )
        residue = fold_signed_fermat(base.residue + correction, width)
        return FermatBinaryFoldAction(width, base.length, residue)

    def triple_fold(
        self, width: int, *, max_nodes: int = MAX_BINARY_SLP_NODES
    ) -> FermatTripleFoldObservation:
        """Observe the fold of three times the source without claiming word shape."""
        folded = self.fold(width, max_nodes=max_nodes)
        residue = fold_signed_fermat(3 * folded.residue, width)
        return FermatTripleFoldObservation(width, folded.length, residue)

    def radial_width_observation(
        self, *, work_budget: int = MAX_RADIAL_WORK
    ) -> RadialWidthObservation:
        """Compare this exact source with the alternating tripling threshold."""
        work_budget = require_integer(
            work_budget, "radial source work budget", 1, MAX_RADIAL_WORK
        )
        snapshot = self._snapshot
        node_count = len(snapshot.nodes)
        if node_count > MAX_BINARY_SLP_NODES or node_count > work_budget:
            raise ValueError(("radial-source-node-budget", node_count, work_budget))
        length = self.source_length
        if length < 1:
            raise ValueError("radial width requires a positive source word")
        work = [0]
        if self._source_bit(length - 1, work_budget=work_budget, work_meter=work) != 1:
            raise ValueError("radial source word must have a canonical leading one")
        if length == 1:
            return RadialWidthObservation(1, -1, 2)

        summaries: list[
            tuple[
                tuple[_PeriodicCompare, _PeriodicCompare],
                tuple[_PeriodicCompare, _PeriodicCompare],
            ]
        ] = []
        for node in snapshot.nodes:
            if node.kind == "EMPTY":
                self._tick_radial(work, work_budget, 4)
                identity = _PeriodicCompare.identity()
                summaries.append(((identity, identity), (identity, identity)))
            elif node.kind == "TERM":
                self._tick_radial(work, work_budget, 4)
                summaries.append(
                    (
                        (
                            _terminal_compare(node.symbol, 0),
                            _terminal_compare(node.symbol, 1),
                        ),
                        (
                            _terminal_compare(node.symbol, 0),
                            _terminal_compare(node.symbol, 1),
                        ),
                    )
                )
            elif node.kind == "CONCAT":
                self._tick_radial(work, work_budget, 8)
                left_summary = summaries[node.left]
                right_summary = summaries[node.right]
                forward = (
                    left_summary[0][0].then(right_summary[0][0]),
                    left_summary[0][1].then(right_summary[0][1]),
                )
                reverse = (
                    right_summary[1][0].then(left_summary[1][0]),
                    right_summary[1][1].then(left_summary[1][1]),
                )
                summaries.append((forward, reverse))
            elif node.kind == "REPEAT":
                self._tick_radial(work, work_budget, 4)
                child = summaries[node.child]
                forward = (
                    child[0][0].repeat(node.count),
                    child[0][1].repeat(node.count),
                )
                reverse = (
                    child[1][0].repeat(node.count),
                    child[1][1].repeat(node.count),
                )
                summaries.append((forward, reverse))
            else:
                raise ValueError("unknown SLP node kind")

        tail = 2 if length % 2 == 0 else 3
        prefix = length - tail
        total = _PeriodicCompare.identity()
        visits = work
        run_count = len(self._runs)
        event_work = 2 * run_count * (run_count.bit_length() + 4)
        if event_work > work_budget - visits[0]:
            raise ValueError(("radial-source-work-budget", work_budget))
        self._tick_radial(visits, work_budget, event_work)
        if prefix:
            for low, high, flipped in _edit_segments(
                0,
                prefix,
                self._runs,
                msb_coordinates=True,
                source_length=length,
            ):
                part = _fold_two_adic_periodic_interval(
                    snapshot,
                    length - high,
                    length - low,
                    source_flip=flipped,
                    summaries=summaries,
                    max_visits=work_budget,
                    total_visits=visits,
                )
                total = total.then(part)

        prefix_mismatch = total.first[0]
        if prefix_mismatch is not None:
            comparison = prefix_mismatch[1]
        else:
            suffix = (1, 1) if length % 2 == 0 else (1, 1, 0)
            comparison = 0
            for index, expected in enumerate(suffix):
                source_position = tail - index - 1
                actual = self._source_bit(
                    source_position,
                    work_budget=work_budget,
                    work_meter=visits,
                )
                if actual != expected:
                    comparison = 1 if actual > expected else -1
                    break
        growth = 2 if comparison >= 0 else 1
        return RadialWidthObservation(length, comparison, length + growth)

    def _source_bit(
        self,
        position: int,
        *,
        work_budget: int,
        work_meter: list[int] | None = None,
    ) -> int:
        if type(position) is not int or not 0 <= position < self.source_length:
            raise IndexError(position)
        visits = 0

        def visit() -> None:
            nonlocal visits
            visits += 1
            if work_meter is not None:
                self._tick_radial(work_meter, work_budget)
            elif visits > work_budget:
                raise ValueError(("source-bit-work-budget", work_budget))

        base = symbol_at(
            self._snapshot,
            self._snapshot.root,
            position,
            on_visit=visit,
        )
        if work_meter is not None:
            self._tick_radial(work_meter, work_budget, len(self._runs))
        flipped = sum(run.start <= position < run.end for run in self._runs) & 1
        return base ^ flipped

    @staticmethod
    def _tick_radial(work: list[int], work_budget: int, amount: int = 1) -> None:
        work[0] += amount
        if work[0] > work_budget:
            raise ValueError(("radial-source-work-budget", work_budget))

    @staticmethod
    def _signed_two_power_mod(exponent: int, width: int) -> int:
        quotient, remainder = divmod(exponent, width)
        return (1 << remainder) * (-1 if quotient & 1 else 1)


__all__ = [
    "FermatTripleFoldObservation",
    "GuardedBinarySource",
    "GuardedXorRun",
    "RadialWidthObservation",
]
