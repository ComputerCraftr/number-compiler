"""Source-certified, powered *spatial* LT/EQ/GT output of the T**2 rule.

A boundary-width clock identifies where an output pair is located, but does
not determine the pair digits.  This module supplies the missing *emission*
morphism on protected periodic source regions.  The exact radius-one Boolean/F5
stencil evolves two digit rings; a finite unary temporal orbit is powered by
lasso reduction.  The resulting *spatial* bank word is represented as
CONCAT(REPEAT(motif, count), suffix), without the target-integer SLP.

Both source halos (including the next step needed by conditional borrows) are
proved by exact SLP folds.  Neither a residue collision nor a matching edge
phase is permitted to authorize a nonperiodic interior or an infinite finite-
source certificate.  The guard grows with the requested temporal horizon.
"""

from __future__ import annotations

from collections.abc import Hashable, Mapping
from contextlib import ExitStack
from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.functions.finite_observer import (
    FiniteOrbitMoore,
    minimize_finite_orbit,
    partition_representatives,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)

from ._temporal_bank_authority import (
    FrozenMap,
    _SourceAuthorizedRecord,
    issue_source_record,
    validate_source_record,
)
from .protected_temporal_bank import (
    MAX_PROTECTED_PERIOD,
    MAX_PROTECTED_TEMPORAL_STATES,
    PERIODIC_CHANNELS,
    PeriodicBankFrame,
    _advance,
    certified_periodic_regions,
)
from .temporal_hashlife import edge_phase, growth_ports
from .temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    certified_residue_action,
    decimal_residues_from_slp,
)

_PeriodicState = tuple[tuple[int, ...], tuple[int, ...], int, int, int]


def _frame_at(
    state: tuple[tuple[int, ...], tuple[int, ...], int, int, int],
    successor: tuple[tuple[int, ...], tuple[int, ...], int, int, int],
    spatial_offset: int,
) -> PeriodicBankFrame:
    left, right, left_offset, right_offset, phase = state
    next_left, next_right, next_left_offset, next_right_offset, _ = successor
    left_index = (left_offset + spatial_offset) % len(left)
    right_index = (right_offset - spatial_offset) % len(right)
    future_left_index = (next_left_offset + spatial_offset) % len(next_left)
    future_right_index = (next_right_offset - spatial_offset) % len(next_right)
    before = (left[left_index], right[right_index])
    after = (next_left[future_left_index], next_right[future_right_index])
    birth_left, birth_right = growth_ports(phase, 1)
    return frame_from_digits(before, after, birth_left, birth_right)


def _frame_output_label(frame: PeriodicBankFrame) -> tuple[Hashable, ...]:
    """Encode the complete frame with immutable primitive tuple labels."""
    return (
        frame.pair,
        frame.f5,
        frame.lt_low,
        frame.lt_high,
        frame.eq,
        frame.gt_low,
        frame.gt_high,
        frame.digits,
        frame.next_digits,
        frame.carry_left,
        frame.carry_right,
        frame.carry_xor,
        frame.borrow_left,
        frame.borrow_right,
        frame.growth_left,
        frame.growth_right,
    )


def _row_output_label(
    row: tuple[PeriodicBankFrame, ...],
) -> tuple[tuple[Hashable, ...], ...]:
    """Convert one spatial row to labels accepted by the finite observer."""
    return tuple(_frame_output_label(frame) for frame in row)


def frame_from_digits(
    before: tuple[int, int],
    after: tuple[int, int],
    birth_left: int,
    birth_right: int,
) -> PeriodicBankFrame:
    """Shared exact Boolean five-band and conditional-borrow output encoder."""
    pair = sum(before)
    return PeriodicBankFrame(
        pair,
        pair % 5,
        int(pair < 5),
        int(5 <= pair <= 8),
        int(pair == 9),
        int(10 <= pair <= 14),
        int(15 <= pair <= 18),
        before,
        after,
        int(before[0] >= 5),
        int(before[1] >= 5),
        int(before[0] >= 5) ^ int(before[1] >= 5),
        (int(after[0] < before[0]), int(after[0] < before[0] + 1)),
        (int(after[1] < before[1]), int(after[1] < before[1] + 1)),
        birth_left,
        birth_right,
    )


def _authorized_frame_at(
    record: _SourceAuthorizedRecord,
    frames: tuple[PeriodicBankFrame, ...],
    pair_offset: int,
) -> PeriodicBankFrame:
    """Read one frame after validating the packet's source authority."""
    validate_source_record(record)
    if type(pair_offset) is not int or not 0 <= pair_offset < len(frames):
        raise IndexError(pair_offset)
    return frames[pair_offset]


def _least_period(frames: tuple[PeriodicBankFrame, ...]) -> int:
    """Minimize the *complete* spatial emission, not just its GT-high bit."""
    n = len(frames)
    return next(
        d
        for d in range(1, n + 1)
        if n % d == 0 and all(frames[i] == frames[i % d] for i in range(n))
    )


def _joint_moore_counts(
    outputs: tuple[tuple[PeriodicBankFrame, ...], ...],
    successors: tuple[int, ...],
    joint_class_count: int,
    *,
    ledger: ResourceLedger | None = None,
) -> FrozenMap[str, int]:
    """Project exact Moore class counts from one complete emitted-row orbit.

    The joint minimizer is counted by its caller.  This helper invokes one
    scalar-output minimizer per channel, so both constructor and scalar-visit
    counters are updated at those actual operations.
    """

    def refinement_work(size: int) -> None:
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_SWEEPS
            )
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_ROUNDS
            )
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_STATE_VISITS,
                size,
            )

    counts: dict[str, int] = {}
    scalar_visits = sum(len(row) for row in outputs)
    for channel in PERIODIC_CHANNELS:
        labels = tuple(tuple(frame.scalar(channel) for frame in row) for row in outputs)
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS
            )
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS,
                scalar_visits,
            )
        counts[channel] = minimize_finite_orbit(
            successors,
            labels,
            max_states=MAX_PROTECTED_TEMPORAL_STATES,
            on_refinement=refinement_work if ledger is not None else None,
        ).class_count
    counts["joint"] = joint_class_count
    return FrozenMap(counts)


@dataclass(frozen=True, slots=True)
class CertifiedSpatialBankMorphism(_SourceAuthorizedRecord):
    """A source-bound spatial word `motif**repeats + suffix` at time T**(2D).

    Pair positions refer to the *entry* word: the final positions are shifted
    by ``left_births``.  The output is a spatial word, unlike the earlier
    ProtectedPeriodicBank which is a temporal word for ONE pointed pair.
    """

    physical_prefix: int
    f_steps: int
    phase_in: int
    phase_out: int
    width_in: int
    width_out: int
    pair_start: int
    pair_count: int
    left_births: int
    right_births: int
    left_region: tuple[int, int]
    right_region: tuple[int, int]
    input_period: int
    motif: tuple[PeriodicBankFrame, ...]
    repeats: int
    suffix: tuple[PeriodicBankFrame, ...]
    temporal_preperiod: int | None
    temporal_period: int | None
    moore_classes: Mapping[str, int] | None
    residue_action: CertifiedResidueTemporalAction

    def __post_init__(self) -> None:
        if self.moore_classes is not None and not isinstance(
            self.moore_classes, FrozenMap
        ):
            object.__setattr__(self, "moore_classes", FrozenMap(self.moore_classes))
        if self.pair_count != len(self.motif) * self.repeats + len(self.suffix):
            raise ValueError(
                "spatial bank CONCAT/REPEAT length does not match its request"
            )
        if not self.motif:
            raise ValueError("spatial bank requires a nonempty emission motif")

    @property
    def final_pair_start(self) -> int:
        return self.pair_start + self.left_births

    @property
    def spatial_period(self) -> int:
        return len(self.motif)

    def at(self, pair_offset: int) -> PeriodicBankFrame:
        validate_source_record(self)
        return self._at_trusted(pair_offset)

    def _at_trusted(self, pair_offset: int) -> PeriodicBankFrame:
        """Read one frame after the caller has validated the source authority."""
        if type(pair_offset) is not int or not 0 <= pair_offset < self.pair_count:
            raise IndexError(pair_offset)
        motif_span = len(self.motif) * self.repeats
        if pair_offset < motif_span:
            return self.motif[pair_offset % len(self.motif)]
        return self.suffix[pair_offset - motif_span]

    def counts(self) -> dict[str, int]:
        validate_source_record(self)
        return {
            channel: (
                self.repeats * sum(frame.scalar(channel) for frame in self.motif)
                + sum(frame.scalar(channel) for frame in self.suffix)
            )
            for channel in PERIODIC_CHANNELS
        }

    def output_word(self, channel: str) -> tuple[tuple[int, ...], int, tuple[int, ...]]:
        """Exact CONCAT(REPEAT(motif, repeats), suffix) channel emission."""
        validate_source_record(self)
        if channel not in PERIODIC_CHANNELS:
            raise ValueError("unknown GT/EQ/LT bank output channel")
        return (
            tuple(frame.scalar(channel) for frame in self.motif),
            self.repeats,
            tuple(frame.scalar(channel) for frame in self.suffix),
        )

    def spatial_walsh64(self, channel: str, *, start: int = 0) -> tuple[int, ...]:
        """Demand 64 spatial lanes; never materialize the entire word."""
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        validate_source_record(self)
        if channel not in PERIODIC_CHANNELS:
            raise ValueError("unknown GT/EQ/LT bank output channel")
        if type(start) is not int or start < 0 or start + 64 > self.pair_count:
            raise ValueError("64 spatial lanes are outside the certified bank word")
        values = [self._at_trusted(start + i).scalar(channel) for i in range(64)]
        # F5 is a 5-valued port; use the linear transform of its exact values.
        if channel == "f5":
            return tuple(
                sum(
                    (1 if (i & j).bit_count() % 2 == 0 else -1) * values[j]
                    for j in range(64)
                )
                % 5
                for i in range(64)
            )
        mask = sum(value << i for i, value in enumerate(values))
        return walsh64_mod5(mask)


@dataclass(frozen=True, slots=True)
class ExactPointedBankWindow(_SourceAuthorizedRecord):
    """Finite source-derived bank word, without a claimed pumped interior.

    This explicitly materializes at most a small requested OUTPUT window, not
    the full target integer.  Its cells come from exact powered F cones. The
    next-frame digit responses follow the same moving source-relative ray as
    the protected temporal bank; they are not a full innovation-borrow tape.
    """

    physical_prefix: int
    f_steps: int
    phase_in: int
    width_in: int
    width_out: int
    final_pair_start: int
    frames: tuple[PeriodicBankFrame, ...]
    residue_action: CertifiedResidueTemporalAction
    open_used: bool = False
    open_moore_classes: int | None = None
    open_input_period: int | None = None

    def __post_init__(self) -> None:
        if type(self.open_used) is not bool:
            raise ValueError("open-bank use marker must be Boolean")
        if self.open_moore_classes is not None and (
            type(self.open_moore_classes) is not int or self.open_moore_classes < 1
        ):
            raise ValueError("open-bank Moore class count must be positive")
        if self.open_input_period is not None and (
            type(self.open_input_period) is not int or self.open_input_period < 1
        ):
            raise ValueError("open-bank input period must be positive")
        if not self.open_used and (
            self.open_moore_classes is not None or self.open_input_period is not None
        ):
            raise ValueError("unused open bank cannot publish quotient metadata")

    @property
    def pair_count(self) -> int:
        return len(self.frames)

    def at(self, pair_offset: int) -> PeriodicBankFrame:
        return _authorized_frame_at(self, self.frames, pair_offset)

    def counts(self) -> dict[str, int]:
        validate_source_record(self)
        return {
            channel: sum(frame.scalar(channel) for frame in self.frames)
            for channel in PERIODIC_CHANNELS
        }

    def output_word(self, channel: str) -> tuple[tuple[int, ...], int, tuple[int, ...]]:
        validate_source_record(self)
        if channel not in PERIODIC_CHANNELS:
            raise ValueError("unknown bank output channel")
        return (tuple(frame.scalar(channel) for frame in self.frames), 1, ())


def certified_spatial_bank_morphism(
    arena: SLPArena,
    source_root: int,
    phase: int,
    pair_start: int,
    pair_count: int,
    f_steps: int,
    period: int,
    *,
    physical_prefix: int = 0,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> CertifiedSpatialBankMorphism:
    """Certify and power a complete spatial LT/EQ/GT bank on periodic halos.

    This does not call a target-root producer, examine completed endpoints,
    extrapolate a known modulo-99 residue, or assume independent ingress bits.
    One exact SLP period guard covers every causal cone across the full
    requested pair interval and the additional frame for borrow responses.
    """
    if type(source_root) is not int or not 0 <= source_root < len(arena.nodes):
        raise ValueError("source-bound bank needs an existing SLP root")
    if type(phase) is not int or phase not in range(4):
        raise ValueError("source-bound bank needs an authenticated border phase")
    if type(physical_prefix) is not int or physical_prefix < 0:
        raise ValueError("invalid physical prefix")
    if type(f_steps) is not int or f_steps < 0:
        raise ValueError("nonnegative two-step horizon required")
    if type(period) is not int or not 1 <= period <= MAX_PROTECTED_PERIOD:
        raise ValueError("periodic bank uses a decimal period of 1..8")
    if (
        type(pair_start) is not int
        or type(pair_count) is not int
        or pair_start < 0
        or pair_count < 1
    ):
        raise ValueError("bank interval requires a nonempty source-relative pair range")
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("periodic bank requires both resource handles")
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
        raise ValueError("source has no authenticated four-phase border cylinder")
    if 2 * (pair_start + pair_count - 1) >= width - 1:
        raise ValueError("bank interval must lie strictly before the entry-word center")

    left_births, right_births = growth_ports(phase, f_steps)
    width_out = width + left_births + right_births
    if 2 * (pair_start + left_births + pair_count - 1) >= width_out - 1:
        raise ValueError("bank interval crosses the output center")
    depth = f_steps + 1
    lnext, rnext = growth_ports(phase, depth)
    right_skew = rnext - lnext
    left_origin = pair_start
    right_origin = width - 1 - pair_start
    left_region = (left_origin - depth, left_origin + pair_count + depth)
    right_region = (
        right_origin - (pair_count - 1) + right_skew - depth,
        right_origin + right_skew + depth + 1,
    )
    if (
        left_region[0] < 0
        or left_region[1] > width
        or right_region[0] < 0
        or right_region[1] > width
        or left_origin + period > width
        or right_origin + period > width
    ):
        raise ValueError("source lacks complete moving causal halos for the bank word")
    left_pattern = tuple(
        symbol_at(arena, source_root, left_origin + i) for i in range(period)
    )
    right_pattern = tuple(
        symbol_at(arena, source_root, right_origin + i) for i in range(period)
    )
    if not all(
        certified_periodic_regions(
            arena,
            source_root,
            (
                (*left_region, left_origin, left_pattern),
                (*right_region, right_origin, right_pattern),
            ),
            ledger=ledger,
            scratch_owner=scratch_owner,
        )
    ):
        raise ValueError(
            "source periodic halo cannot authorize the spatial bank morphism"
        )

    with ExitStack() as retained:
        state: _PeriodicState = (left_pattern, right_pattern, 0, 0, phase)

        def retain_state() -> None:
            if ledger is None:
                return
            retained.enter_context(
                ledger.reservation(
                    cast(int, scratch_owner), entries=4, nodes=16 + 8 * period
                )
            )

        retain_state()
        states: list[_PeriodicState] = [state]
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES
            )
        indices: dict[_PeriodicState, int] = {state: 0}
        cycle_begin: int | None = None
        cycle_size: int | None = None
        while len(states) <= depth:
            if len(states) >= MAX_PROTECTED_TEMPORAL_STATES:
                raise ValueError(
                    "temporal bank exceeds the proven finite-state search budget"
                )
            nxt, _ = _advance(state, ledger=ledger)
            if nxt in indices:
                cycle_begin = indices[nxt]
                cycle_size = len(states) - cycle_begin
                break
            retain_state()
            indices[nxt] = len(states)
            states.append(nxt)
            if ledger is not None:
                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES
                )
            state = nxt

        def at_time(t: int) -> tuple[tuple[int, ...], tuple[int, ...], int, int, int]:
            if t < len(states):
                return states[t]
            if cycle_begin is None or cycle_size is None:
                raise AssertionError("temporal bank state missing without closed cycle")
            return states[cycle_begin + (t - cycle_begin) % cycle_size]

        joint_moore: FiniteOrbitMoore | None = None
        output_width = min(period, pair_count)
        if cycle_begin is None or cycle_size is None or pair_count < period:
            source_state = at_time(f_steps)
            next_state = at_time(depth)
            spatial_frames = tuple(
                _frame_at(source_state, next_state, i) for i in range(output_width)
            )
            moore_classes = None
        else:
            if ledger is not None:
                retained.enter_context(
                    ledger.reservation(
                        cast(int, scratch_owner),
                        entries=8 * len(states),
                        nodes=16 * len(states) * period,
                    )
                )
            temporal_successors = tuple(
                i + 1 if i + 1 < len(states) else cycle_begin
                for i in range(len(states))
            )
            temporal_outputs = tuple(
                tuple(
                    _frame_at(state, states[temporal_successors[i]], j)
                    for j in range(period)
                )
                for i, state in enumerate(states)
            )
            temporal_output_labels = tuple(
                _row_output_label(row) for row in temporal_outputs
            )

            def record_joint_refinement(size: int) -> None:
                if ledger is not None:
                    ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_SWEEPS
                    )
                    ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_ROUNDS
                    )
                    ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_STATE_VISITS,
                        size,
                    )

            if ledger is not None:
                # Count the invocation, including a failed refinement attempt.
                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS
                )
            joint_moore = minimize_finite_orbit(
                temporal_successors,
                temporal_output_labels,
                max_states=MAX_PROTECTED_TEMPORAL_STATES,
                on_refinement=(record_joint_refinement if ledger is not None else None),
            )
            target_class = joint_moore.advance(joint_moore.class_of(0), f_steps)
            representatives = partition_representatives(
                joint_moore.class_ids, joint_moore.class_count
            )
            # The class action selects the emitted row used for production;
            # raw lasso traversal is retained only as a differential invariant.
            spatial_frames = temporal_outputs[representatives[target_class]]
            if _row_output_label(spatial_frames) != joint_moore.output(target_class):
                raise AssertionError("temporal Moore representative changed its output")
            expected_frames = tuple(
                _frame_at(at_time(f_steps), at_time(depth), i) for i in range(period)
            )
            if spatial_frames != expected_frames:
                raise AssertionError("temporal Moore action changed the exact bank row")
            moore_classes = _joint_moore_counts(
                temporal_outputs,
                temporal_successors,
                joint_moore.class_count,
                ledger=ledger,
            )
        minimal_period = _least_period(spatial_frames)
        motif = spatial_frames[:minimal_period]
        copies, tail = divmod(pair_count, minimal_period)
        residues = decimal_residues_from_slp(
            arena, source_root, ledger=ledger, scratch_owner=scratch_owner
        )
        residue_action = certified_residue_action(
            phase=phase,
            width=width,
            duration=2 * f_steps,
            source_mod99=residues[0],
            source_mod198=residues[1],
        )
        issue_source_record(
            residue_action,
            arena,
            source_root,
            source_generation=physical_prefix,
        )
        if residue_action.width_out != width_out:
            raise AssertionError(
                "spatial source guard and modulo-99 width action disagree"
            )
        result = CertifiedSpatialBankMorphism(
            physical_prefix,
            f_steps,
            phase,
            (phase + 2 * f_steps) % 4,
            width,
            width_out,
            pair_start,
            pair_count,
            left_births,
            right_births,
            left_region,
            right_region,
            period,
            motif,
            copies,
            spatial_frames[:tail],
            cycle_begin,
            cycle_size,
            moore_classes,
            residue_action,
        )
        record = issue_source_record(
            result, arena, source_root, source_generation=physical_prefix
        )
        return record


__all__ = [
    "CertifiedSpatialBankMorphism",
    "ExactPointedBankWindow",
    "certified_spatial_bank_morphism",
    "frame_from_digits",
]
