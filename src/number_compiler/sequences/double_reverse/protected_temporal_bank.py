"""Source-certified periodic LT/EQ/GT bank for the 2rev10 T**2 cellular rule.

This is a *temporal* action on two independent oriented digit periods. It is
only authorized for a finite horizon whose complete causal cones lie in exact
periodic patches of the ORIGINAL SLP. The two-cell border supplies the skew
left/right birth clock but never supplies an invented inward carry bit.

An eventual period in the finite periodic machine gives a CONCAT/REPEAT
program of synchronized five-band, F5, threshold carry and conditional
aligned-difference borrow outputs. It does NOT certify an infinite trajectory
when the source's protected halo is finite. No big integer or digit tape is
materialized for guard or powered output.
"""

from __future__ import annotations

from collections.abc import Mapping
from contextlib import ExitStack, nullcontext
from dataclasses import dataclass
from typing import TypeAlias, cast

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)

from ._temporal_bank_authority import (
    FrozenMap,
    _SourceAuthorizedRecord,
    issue_source_record,
)
from .stencil_moore import stencil_cell
from .temporal_hashlife import edge_phase, growth_ports

PERIODIC_CHANNELS = (
    "lt_low",
    "lt_high",
    "eq",
    "gt_low",
    "gt_high",
    "f5",
    "carry_left",
    "carry_right",
    "carry_xor",
    "borrow_left_0",
    "borrow_left_1",
    "borrow_right_0",
    "borrow_right_1",
    "growth_left",
    "growth_right",
)
MAX_PROTECTED_PERIOD = 8
MAX_PROTECTED_TEMPORAL_STATES = 4096


@dataclass(frozen=True, slots=True)
class _Match:
    """Exact Boolean pattern-matching monoid, for all starting phases."""

    length: int
    matches: tuple[bool, ...]

    @classmethod
    def identity(cls, period: int) -> _Match:
        return cls(0, (True,) * period)

    def then(self, other: _Match) -> _Match:
        if len(self.matches) != len(other.matches):
            raise ValueError("incompatible periodic match actions")
        width = len(self.matches)
        return _Match(
            self.length + other.length,
            tuple(
                self.matches[i] and other.matches[(i + self.length) % width]
                for i in range(width)
            ),
        )

    def power(self, count: int) -> _Match:
        if type(count) is not int or count < 0:
            raise ValueError("negative periodic repeat count")
        result = self.identity(len(self.matches))
        block = self
        while count:
            if count & 1:
                result = result.then(block)
            count >>= 1
            if count:
                block = block.then(block)
        return result


def certified_periodic_region(
    arena: SLPArena,
    root: int,
    lo: int,
    hi: int,
    origin: int,
    pattern: tuple[int, ...],
    *,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> bool:
    """Check every digit of [lo,hi) by a complete, non-hashing SLP fold.

    A period is indexed from `origin` rather than the beginning of the source.
    Full REPEAT nodes are processed by binary monoid composition.
    """
    return certified_periodic_regions(
        arena,
        root,
        ((lo, hi, origin, pattern),),
        ledger=ledger,
        scratch_owner=scratch_owner,
    )[0]


def certified_periodic_regions(
    arena: SLPArena,
    root: int,
    regions: tuple[tuple[int, int, int, tuple[int, ...]], ...],
    *,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> tuple[bool, ...]:
    """Certify several source halos in one shared SLP summary traversal."""
    if type(regions) is not tuple or not regions:
        raise ValueError("periodic guards require at least one region")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("periodic source root is invalid")
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("periodic guard requires both resource handles")
    width = arena.nodes[root].length
    for lo, hi, origin, pattern in regions:
        if (
            type(pattern) is not tuple
            or not pattern
            or len(pattern) > MAX_PROTECTED_PERIOD
            or any(type(d) is not int or not 0 <= d <= 9 for d in pattern)
        ):
            raise ValueError("period must contain 1..8 decimal digits")
        if (
            type(lo) is not int
            or type(hi) is not int
            or type(origin) is not int
            or not 0 <= lo <= hi <= width
        ):
            raise ValueError("periodic halo extends outside the authenticated source")
    bound = len(arena.nodes)
    pattern_cells = sum(len(pattern) for _, _, _, pattern in regions)
    context = (
        nullcontext()
        if ledger is None
        else ledger.reservation(
            cast(int, scratch_owner),
            entries=4 * (bound + 1),
            nodes=(8 + 2 * pattern_cells + 4 * len(regions)) * (bound + 1),
        )
    )
    with context:

        def terminal_summary(symbol: int) -> tuple[_Match, ...]:
            return tuple(
                _Match(1, tuple(symbol == digit for digit in pattern))
                for _, _, _, pattern in regions
            )

        def concatenate_summaries(
            left: tuple[_Match, ...], right: tuple[_Match, ...]
        ) -> tuple[_Match, ...]:
            return tuple(
                first.then(second) for first, second in zip(left, right, strict=True)
            )

        def repeat_summary(child: tuple[_Match, ...], count: int) -> tuple[_Match, ...]:
            return tuple(summary.power(count) for summary in child)

        memo = fold_slp_dag(
            arena,
            root,
            empty_value=tuple(
                _Match.identity(len(pattern)) for _, _, _, pattern in regions
            ),
            terminal_value=terminal_summary,
            concatenate=concatenate_summaries,
            repeat=repeat_summary,
            on_reduce=(
                None
                if ledger is None
                else lambda _node: ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_GUARD_NODES
                )
            ),
        )
        answer: list[bool] = []
        for index, (lo, hi, origin, pattern) in enumerate(regions):

            def full_value(node: int, _reverse: bool, selected: int = index) -> _Match:
                return memo[node][selected]

            result = fold_slp_interval(
                arena,
                root,
                lo,
                hi,
                identity=_Match.identity(len(pattern)),
                length=lambda node: arena.nodes[node].length,
                full_value=full_value,
                compose=lambda left, right: left.then(right),
                repeat=lambda value, count: value.power(count),
                on_visit=(
                    None
                    if ledger is None
                    else lambda: ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_INTERVAL_VISITS
                    )
                ),
            )
            answer.append(result.matches[(lo - origin) % len(pattern)])
        return tuple(answer)


@dataclass(frozen=True, slots=True)
class PeriodicBankFrame:
    """Source-derived temporal ports for one symmetric outer-to-inner pair."""

    pair: int
    f5: int
    lt_low: int
    lt_high: int
    eq: int
    gt_low: int
    gt_high: int
    digits: tuple[int, int]
    next_digits: tuple[int, int]
    carry_left: int
    carry_right: int
    carry_xor: int
    borrow_left: tuple[int, int]
    borrow_right: tuple[int, int]
    growth_left: int
    growth_right: int

    def __post_init__(self) -> None:
        if self.pair != sum(self.digits) or not 0 <= self.pair <= 18:
            raise ValueError("temporal bank pair sum is invalid")
        masks = (
            int(self.pair < 5),
            int(5 <= self.pair <= 8),
            int(self.pair == 9),
            int(10 <= self.pair <= 14),
            int(15 <= self.pair <= 18),
        )
        if masks != (self.lt_low, self.lt_high, self.eq, self.gt_low, self.gt_high):
            raise ValueError("LT/EQ/GT bank mask is inconsistent")
        if self.f5 != self.pair % 5:
            raise ValueError("pair F5 residue is inconsistent")
        if self.carry_xor != (self.carry_left ^ self.carry_right):
            raise ValueError("reflected carry XOR is inconsistent")
        if self.growth_left not in (0, 1) or self.growth_right not in (0, 1):
            raise ValueError("independent birth channels must be Boolean")
        for before, after, response in zip(
            self.digits,
            self.next_digits,
            (self.borrow_left, self.borrow_right),
            strict=True,
        ):
            if response != (int(after < before), int(after < before + 1)):
                raise ValueError("conditional borrow response is inconsistent")

    def scalar(self, name: str) -> int:
        if name == "growth":
            return self.growth
        if name not in PERIODIC_CHANNELS:
            raise ValueError("unknown temporal port name")
        if name.startswith("borrow_left"):
            return self.borrow_left[int(name[-1])]
        if name.startswith("borrow_right"):
            return self.borrow_right[int(name[-1])]
        return int(getattr(self, name))

    @property
    def growth(self) -> int:
        """Aggregate births for callers; this 0..2 value is not a bit channel."""
        return self.growth_left + self.growth_right


_PeriodicState: TypeAlias = tuple[tuple[int, ...], tuple[int, ...], int, int, int]


def _advance(
    state: _PeriodicState, *, ledger: ResourceLedger | None = None
) -> tuple[_PeriodicState, PeriodicBankFrame]:
    left, right, offset_left, offset_right, phase = state
    left_new = tuple(
        stencil_cell(left[(i - 1) % len(left)], left[i], left[(i + 1) % len(left)])
        for i in range(len(left))
    )
    right_new = tuple(
        stencil_cell(right[(i - 1) % len(right)], right[i], right[(i + 1) % len(right)])
        for i in range(len(right))
    )
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_STENCIL_EVALUATIONS,
            3 * (len(left) + len(right)),
        )
    birth_left, birth_right = growth_ports(phase, 1)
    # A Hashlife output at index k is F of source center k-L. The
    # left symmetric cell follows one fixed source ray. The right symmetric
    # cell follows the skew ray delta=R-L: this is the birth-clock term
    # that cannot be erased by an independent right-edge automaton.
    next_left_index = offset_left
    next_right_index = (offset_right + birth_right - birth_left) % len(right)
    before = (left[offset_left], right[offset_right])
    after = (left_new[next_left_index], right_new[next_right_index])
    pair = sum(before)
    carries = tuple(int(d >= 5) for d in before)
    frame = PeriodicBankFrame(
        pair,
        pair % 5,
        int(pair < 5),
        int(5 <= pair <= 8),
        int(pair == 9),
        int(10 <= pair <= 14),
        int(15 <= pair <= 18),
        before,
        after,
        carries[0],
        carries[1],
        carries[0] ^ carries[1],
        (int(after[0] < before[0]), int(after[0] < before[0] + 1)),
        (int(after[1] < before[1]), int(after[1] < before[1] + 1)),
        birth_left,
        birth_right,
    )
    return (
        left_new,
        right_new,
        next_left_index,
        next_right_index,
        (phase + 2) % 4,
    ), frame


def _moore_counts(
    frames: tuple[PeriodicBankFrame, ...],
    next_indices: tuple[int, ...],
    *,
    ledger: ResourceLedger | None = None,
) -> dict[str, int]:
    """Output-aware future Moore refinement on the *closed* finite orbit."""
    if len(frames) != len(next_indices):
        raise ValueError("Moore state/transition length mismatch")
    answer: dict[str, int] = {}
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS
        )
    for channel in (*PERIODIC_CHANNELS, "joint"):
        labels: list[object] = (
            [
                (
                    frame.digits,
                    frame.next_digits,
                    tuple(frame.scalar(name) for name in PERIODIC_CHANNELS),
                )
                for frame in frames
            ]
            if channel == "joint"
            else [frame.scalar(channel) for frame in frames]
        )
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS,
                len(frames) * (len(PERIODIC_CHANNELS) if channel == "joint" else 1),
            )
        classes = _canonical(labels, ledger=ledger)
        # Binary lifting of complete future output words. Once the word
        # length reaches the number of reachable states, equality is the
        # stable Moore congruence of this deterministic finite machine.
        # Signatures are interned tuples (no probabilistic hashing).
        jump = next_indices
        represented = 1
        while represented < len(frames):
            if ledger is not None:
                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_SWEEPS
                )
            classes = _canonical(
                [(classes[i], classes[jump[i]]) for i in range(len(frames))],
                ledger=ledger,
            )
            jump = tuple(jump[jump[i]] for i in range(len(frames)))
            represented *= 2
            if ledger is not None:
                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_ROUNDS
                )
        answer[channel] = len(set(classes))
    return answer


def _canonical(
    keys: list[object], *, ledger: ResourceLedger | None = None
) -> tuple[int, ...]:
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_STATE_VISITS,
            len(keys),
        )
    ids: dict[object, int] = {}
    return tuple(ids.setdefault(key, len(ids)) for key in keys)


@dataclass(frozen=True, slots=True)
class ExactTemporalPairPort:
    """One exact final-time source-bound pair, not an infinite bank period."""

    pair_position: int
    width: int
    physical_prefix: int
    f_steps: int
    digits: tuple[int, int]
    pair: int
    f5: int
    lt_low: int
    lt_high: int
    eq: int
    gt_low: int
    gt_high: int
    carry: tuple[int, int]
    reflected_xor: int

    @classmethod
    def from_digits(
        cls,
        pair_position: int,
        width: int,
        physical_prefix: int,
        f_steps: int,
        left: int,
        right: int,
    ) -> ExactTemporalPairPort:
        if any(type(d) is not int or not 0 <= d <= 9 for d in (left, right)):
            raise ValueError("invalid exact pair digit")
        pair = left + right
        c = (int(left >= 5), int(right >= 5))
        return cls(
            pair_position,
            width,
            physical_prefix,
            f_steps,
            (left, right),
            pair,
            pair % 5,
            int(pair < 5),
            int(5 <= pair <= 8),
            int(pair == 9),
            int(10 <= pair <= 14),
            int(15 <= pair <= 18),
            c,
            c[0] ^ c[1],
        )


@dataclass(frozen=True, slots=True)
class ProtectedPeriodicBank(_SourceAuthorizedRecord):
    """Finite-halo, source-root-specific lasso of exact temporal output frames."""

    pair_position: int
    source_width: int
    phase_in: int
    physical_prefix: int
    f_steps: int
    period: int
    left_region: tuple[int, int]
    right_region: tuple[int, int]
    prefix_frames: tuple[PeriodicBankFrame, ...]
    motif: tuple[PeriodicBankFrame, ...]
    repeat_count: int
    suffix: tuple[PeriodicBankFrame, ...]
    moore_classes: Mapping[str, int] | None

    def __post_init__(self) -> None:
        if self.moore_classes is not None and not isinstance(
            self.moore_classes, FrozenMap
        ):
            object.__setattr__(self, "moore_classes", FrozenMap(self.moore_classes))

    @property
    def represented_steps(self) -> int:
        return (
            len(self.prefix_frames)
            + len(self.motif) * self.repeat_count
            + len(self.suffix)
        )

    def at(self, tick: int) -> PeriodicBankFrame:
        if type(tick) is not int or not 0 <= tick < self.f_steps:
            raise IndexError(tick)
        if tick < len(self.prefix_frames):
            return self.prefix_frames[tick]
        tick -= len(self.prefix_frames)
        if self.motif:
            count = len(self.motif) * self.repeat_count
            if tick < count:
                return self.motif[tick % len(self.motif)]
            tick -= count
        return self.suffix[tick]

    def counts(self) -> dict[str, int]:
        return {
            channel: (
                sum(frame.scalar(channel) for frame in self.prefix_frames)
                + self.repeat_count * sum(frame.scalar(channel) for frame in self.motif)
                + sum(frame.scalar(channel) for frame in self.suffix)
            )
            for channel in PERIODIC_CHANNELS
        }


def protected_periodic_bank(
    arena: SLPArena,
    source_root: int,
    phase: int,
    pair_position: int,
    f_steps: int,
    period: int,
    *,
    physical_prefix: int = 0,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> ProtectedPeriodicBank:
    """Prove two moving causal halos and pump the exact pair-port automaton.

    Only a periodicity proven across the *entire* original causal region is
    permitted; no sampled GT-high or boundary clock is accepted as a halo.
    The clock handles every left/right cell birth without inventing a seam.
    """
    if type(f_steps) is not int or f_steps < 1:
        raise ValueError("positive two-step temporal duration required")
    if type(period) is not int or not 1 <= period <= MAX_PROTECTED_PERIOD:
        raise ValueError("protected temporal bank requires period 1..8")
    if type(phase) is not int or phase not in range(4):
        raise ValueError("source must have a certified four-phase boundary")
    if type(source_root) is not int or not 0 <= source_root < len(arena.nodes):
        raise ValueError("source root is invalid")
    if type(pair_position) is not int or pair_position < 0:
        raise ValueError("pair position must be nonnegative")
    if type(physical_prefix) is not int or physical_prefix < 0:
        raise ValueError("physical prefix must be nonnegative")
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("protected bank resource handles are incomplete")
    width = arena.nodes[source_root].length
    if (
        width < 5
        or edge_phase(
            (symbol_at(arena, source_root, 0), symbol_at(arena, source_root, 1)),
            (
                symbol_at(arena, source_root, width - 2),
                symbol_at(arena, source_root, width - 1),
            ),
        )
        != phase
    ):
        raise ValueError("periodic bank source has no certified border phase")
    if 2 * pair_position >= width - 1:
        raise ValueError("symmetric bank coordinate must lie before the center")
    left_origin, right_origin = pair_position, width - 1 - pair_position
    # The left ray is fixed in source coordinates, but the reflected ray
    # acquires the skew shift R_D-L_D. Since its per-tick increment is in
    # {-1,0,1}, the left/right extremes of each causal cone are monotone,
    # and their bounds at D cover every earlier temporal port.
    left_growth, right_growth = growth_ports(phase, f_steps)
    skew = right_growth - left_growth
    left_bounds = (left_origin - f_steps, left_origin + f_steps + 1)
    right_bounds = (right_origin + skew - f_steps, right_origin + skew + f_steps + 1)
    if (
        left_bounds[0] < 0
        or right_bounds[0] < 0
        or left_bounds[1] > width
        or right_bounds[1] > width
    ):
        raise ValueError("source lacks the protected temporal halo")
    if left_origin + period > width or right_origin + period > width:
        raise ValueError("period sampling exceeds the source digit region")
    left_period = tuple(
        symbol_at(arena, source_root, left_origin + i) for i in range(period)
    )
    right_period = tuple(
        symbol_at(arena, source_root, right_origin + i) for i in range(period)
    )
    regions = (
        (*left_bounds, left_origin, left_period),
        (*right_bounds, right_origin, right_period),
    )
    if not all(
        certified_periodic_regions(
            arena,
            source_root,
            regions,
            ledger=ledger,
            scratch_owner=scratch_owner,
        )
    ):
        raise ValueError("source periodic halo does not match its GT/EQ/LT bank")

    with ExitStack() as scratch:
        frames: list[PeriodicBankFrame] = []
        seen: dict[_PeriodicState, int] = {}
        state: _PeriodicState = (left_period, right_period, 0, 0, phase)
        repeat_begin: int | None = None
        # A finite horizon may end before a repeat is found. This is still an
        # exact finite protected action, but NOT a universal Moore certificate.
        while len(frames) < f_steps and state not in seen:
            if len(frames) >= MAX_PROTECTED_TEMPORAL_STATES:
                raise ValueError("protected bank exceeds temporal state budget")
            if ledger is not None:
                scratch.enter_context(
                    ledger.reservation(
                        cast(int, scratch_owner),
                        entries=4,
                        nodes=16 + 8 * period,
                    )
                )
            seen[state] = len(frames)
            state, frame = _advance(state, ledger=ledger)
            frames.append(frame)
            if ledger is not None:
                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES
                )
        if state in seen:
            repeat_begin = seen[state]
        if repeat_begin is None:
            result = ProtectedPeriodicBank(
                pair_position,
                width,
                phase,
                physical_prefix,
                f_steps,
                period,
                left_bounds,
                right_bounds,
                tuple(frames),
                (),
                0,
                (),
                None,
            )
        else:
            start = repeat_begin
            cycle = len(frames) - start
            copies, tail = divmod(f_steps - start, cycle)
            next_indices = tuple(
                i + 1 if i + 1 < len(frames) else start for i in range(len(frames))
            )
            frames_tuple = tuple(frames)
            if ledger is not None:
                scratch.enter_context(
                    ledger.reservation(
                        cast(int, scratch_owner),
                        entries=8 * len(frames),
                        nodes=16 * len(frames),
                    )
                )
            result = ProtectedPeriodicBank(
                pair_position,
                width,
                phase,
                physical_prefix,
                f_steps,
                period,
                left_bounds,
                right_bounds,
                tuple(frames[:start]),
                tuple(frames[start:]),
                copies,
                tuple(frames[start : start + tail]),
                _moore_counts(frames_tuple, next_indices, ledger=ledger),
            )
    if result.represented_steps != f_steps:
        raise AssertionError("pumped bank temporal duration is inconsistent")
    issue_source_record(result, arena, source_root, source_generation=physical_prefix)
    if ledger is not None:
        ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_PUBLICATIONS)
    return result


__all__ = [
    "MAX_PROTECTED_PERIOD",
    "MAX_PROTECTED_TEMPORAL_STATES",
    "PERIODIC_CHANNELS",
    "ExactTemporalPairPort",
    "PeriodicBankFrame",
    "ProtectedPeriodicBank",
    "certified_periodic_region",
    "certified_periodic_regions",
    "protected_periodic_bank",
]
