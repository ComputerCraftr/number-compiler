"""Moving-boundary temporal rings for source-certified 2rev10 digit births.

A fixed source-coordinate open ring is not the same as a ring of the first K
canonical digits at every generation: when digits are born, the latter must
be *recentered*.  This module constructs the actual birth-centered action,
with one genuinely inward digit on each end as its conditional interface.

An inlet that happens to repeat in a finite certified horizon never licenses
an infinite seed trajectory.  Its finite model lasso is a CONDITIONAL action,
and all real-source emissions are checked against independent causal cones.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import TYPE_CHECKING, TypeGuard

from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.automata.word_period import (
    finite_suffix_period,
    primitive_period,
)
from number_compiler.arithmetic.fields.decimal_pair_partition import DecimalPairBand
from number_compiler.resources.metric_keys import double_reverse as metric_keys

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    issue_source_record,
    validate_source_record,
)
from .protected_temporal_bank import PeriodicBankFrame, TemporalBankChannel
from .stencil_moore import stencil_cell
from .temporal_bank_output_morphism import frame_from_digits
from .temporal_birth_induction import (
    CertifiedBirthClock,
    birth_clock_for_source,
    validate_birth_duration,
)
from .temporal_diagonal_induction import (
    ClosedBorderPairReturn,
    FiniteInductionWitness,
    certified_closed_outer_pair_return,
    finite_birth_period_induction,
)
from .temporal_hashlife import growth_ports

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger

    from .source_bound_bank import PointedBankSource

MAX_BIRTH_LAYER_PAIRS = 16
MAX_BIRTH_LAYER_HORIZON = 160
MAX_BIRTH_CONDITIONAL_STATES = 1024
MAX_BIRTH_TEMPORARY_UNITS = 400_000


def _is_birth_ring_state(value: object) -> TypeGuard[BirthRingState]:
    return isinstance(value, BirthRingState)


def _is_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    return type(value) is tuple


def _is_birth_ring_word(value: object) -> TypeGuard[tuple[BirthRingPorts, ...]]:
    return _is_tuple(value) and all(isinstance(port, BirthRingPorts) for port in value)


class BirthReturnBudgetExceeded(ValueError):
    """The conditional birth orbit did not close within its state budget."""


def _birth_strip_workspace_units(pairs: int, horizon: int) -> int:
    """Conservative live-reference bound for all retained source strips."""
    return (horizon + 1) * (4 * pairs + pairs * (pairs + 1)) + 8 * pairs


def _birth_model_workspace_units(pairs: int, max_states: int) -> int:
    """Conservative bound for one conditional orbit and its channel rows."""
    return max_states * (20 * pairs + 8)


def _charge_period_comparisons(ledger: ResourceLedger | None, comparisons: int) -> None:
    if ledger is not None:
        ledger.bump(
            metric_keys.DOUBLE_REVERSE_BIRTH_LAYER_PERIOD_COMPARISONS, comparisons
        )


def _measured_period(values: tuple[object, ...], ledger: ResourceLedger | None) -> int:
    period, comparisons = primitive_period(values)
    _charge_period_comparisons(ledger, comparisons)
    return period


@dataclass(frozen=True, slots=True)
class BirthRingPorts:
    """Source's next inward left and right digit at the current F-step."""

    left_inner: int
    right_inner: int

    def __post_init__(self) -> None:
        if any(
            type(d) is not int or not 0 <= d <= 9
            for d in (self.left_inner, self.right_inner)
        ):
            raise ValueError("birth-ring inputs must be genuine decimal digits")


@dataclass(frozen=True, slots=True)
class BirthRingState:
    """First/last K digits in canonical *moving-boundary* coordinates."""

    left: tuple[int, ...]
    right: tuple[int, ...]
    phase: int

    def __post_init__(self) -> None:
        if (
            not self.left
            or len(self.left) != len(self.right)
            or type(self.phase) is not int
            or self.phase not in (0, 1, 2, 3)
            or any(
                type(d) is not int or not 0 <= d <= 9 for d in self.left + self.right
            )
        ):
            raise ValueError("invalid moving-boundary ring")

    @property
    def pairs(self) -> int:
        return len(self.left)

    def advance(
        self,
        inlet: BirthRingPorts,
    ) -> tuple[BirthRingState, tuple[PeriodicBankFrame, ...]]:
        """One exact F=T² tick, inserting both source-certified edge births."""
        n = self.pairs
        born_left, born_right = growth_ports(self.phase, 1)

        def left_digit(index: int) -> int:
            if index < 0:
                return 0
            if index < n:
                return self.left[index]
            if index == n:
                return inlet.left_inner
            raise AssertionError("left causal stencil escaped one-digit inlet")

        def right_digit(index: int) -> int:
            if index < 0:
                if index == -1:
                    return inlet.right_inner
                raise AssertionError("right causal stencil escaped one-digit inlet")
            if index < n:
                return self.right[index]
            return 0

        left_next = tuple(
            stencil_cell(*(left_digit(j - born_left + delta) for delta in (-1, 0, 1)))
            for j in range(n)
        )
        right_next = tuple(
            stencil_cell(*(right_digit(j + born_right + delta) for delta in (-1, 0, 1)))
            for j in range(n)
        )
        future = BirthRingState(left_next, right_next, (self.phase + 2) % 4)
        frames = tuple(
            frame_from_digits(
                (self.left[j], self.right[n - 1 - j]),
                (left_next[j], right_next[n - 1 - j]),
                born_left,
                born_right,
            )
            for j in range(n)
        )
        return future, frames


def odd_boundary_pairs(
    state: BirthRingState,
    inlet: BirthRingPorts,
) -> tuple[tuple[int, int], ...] | None:
    """Exact intermediate T step's first/last K digit pairs.

    A canonical nonshrinking decimal source can determine these from its
    outer K+1 digits. A conditional synthetic ring may not satisfy that
    guard; return None rather than invent a leading digit after contraction.
    """
    n = state.pairs
    if state.left[0] == 0:
        return None  # the conditional model has left its canonical cylinder
    leading = state.left
    right = state.right
    low = tuple(
        reversed(
            tuple(
                (2 * leading[i] + (int(leading[i - 1] >= 5) if i else 0)) % 10
                for i in range(n)
            )
        )
    )
    units_first = tuple(reversed(right))

    def unit(index: int) -> int:
        return units_first[index] if index < n else inlet.right_inner

    def high_digit(index: int) -> int:
        return (2 * unit(index) + int(unit(index + 1) >= 5)) % 10

    if units_first[0] >= 5:
        high = (1,) + tuple(high_digit(i) for i in range(n - 1))
    else:
        high = tuple(high_digit(i) for i in range(n))
        if high[0] == 0:
            return None  # width contraction requires a separate guard
    return tuple((high[i], low[n - 1 - i]) for i in range(n))


def project_birth_layer(
    deeper: BirthRingState,
) -> tuple[BirthRingState, BirthRingPorts]:
    """Exact (K+1)->K projection; no unproved external inlet is used."""
    if deeper.pairs < 2:
        raise ValueError("birth-layer projection needs a deeper digit pair")
    return (
        BirthRingState(deeper.left[:-1], deeper.right[1:], deeper.phase),
        BirthRingPorts(deeper.left[-1], deeper.right[0]),
    )


def assert_birth_layer_step(
    deeper: BirthRingState,
    inlet: BirthRingPorts,
) -> BirthRingState:
    """Check source-independent commutation and all emitted pair channels."""
    outer, outer_inlet = project_birth_layer(deeper)
    future_deeper, emitted = deeper.advance(inlet)
    future_outer, emitted_outer = outer.advance(outer_inlet)
    projected_future, _ = project_birth_layer(future_deeper)
    if future_outer != projected_future or emitted_outer != emitted[:-1]:
        raise AssertionError("moving-boundary inward action fails to commute")
    return future_deeper


@dataclass(frozen=True, slots=True)
class ConditionalBirthReturn:
    """Return period inside a fully specified periodic *inlet model* only."""

    input_period: int
    preperiod: int
    full_state_period: int
    ordered_pair_period: int
    gt_high_period: int
    carry_xor_period: int
    return_multiplier: int
    conditional_model_states: int
    physical_pair_period: int | None = None
    physical_gt_high_period: int | None = None
    physical_carry_xor_period: int | None = None


@dataclass(frozen=True, slots=True)
class _ConditionalBirthModel:
    """Deterministic conditional lasso, indexed in O(1) after construction."""

    states: tuple[BirthRingState, ...]
    frames: tuple[tuple[PeriodicBankFrame, ...], ...]
    result: ConditionalBirthReturn

    def at(self, steps: int) -> tuple[BirthRingState, tuple[PeriodicBankFrame, ...]]:
        if steps < len(self.states):
            index = steps
        else:
            index = self.result.preperiod + (
                (steps - self.result.preperiod) % self.result.full_state_period
            )
        return self.states[index], self.frames[index]


def _enumerate_conditional_birth_model(
    state: object,
    inlet_motif: object,
    *,
    max_states: int,
    ledger: ResourceLedger | None = None,
) -> _ConditionalBirthModel:
    """Close the entire (state, inlet phase) orbit before publishing a power."""
    if (
        not _is_birth_ring_state(state)
        or state.pairs > MAX_BIRTH_LAYER_PAIRS
        or not _is_birth_ring_word(inlet_motif)
        or not inlet_motif
        or len(inlet_motif) > MAX_BIRTH_LAYER_HORIZON
        or type(max_states) is not int
        or not 1 <= max_states <= MAX_BIRTH_CONDITIONAL_STATES
    ):
        raise ValueError("periodic birth model requires a bounded input word")
    seen: dict[tuple[BirthRingState, int], int] = {}
    states: list[BirthRingState] = []
    frames: list[tuple[PeriodicBankFrame, ...]] = []
    pair_words: list[tuple[tuple[int, int], ...]] = []
    mask_words: list[tuple[int, ...]] = []
    xor_words: list[tuple[int, ...]] = []
    odd_words: list[tuple[tuple[int, int], ...] | None] = []
    current = state
    steps = 0
    while True:
        key = current, steps % len(inlet_motif)
        if key in seen:
            entry = seen[key]
            period = steps - entry
            break
        if steps >= max_states:
            raise BirthReturnBudgetExceeded(
                "conditional moving-boundary return did not close within budget"
            )
        seen[key] = steps
        if ledger is not None:
            ledger.bump(metric_keys.DOUBLE_REVERSE_BIRTH_LAYER_MODEL_STATES)
        inlet = inlet_motif[steps % len(inlet_motif)]
        next_state, frame = current.advance(inlet)
        states.append(current)
        frames.append(frame)
        pair_words.append(
            tuple(
                (current.left[i], current.right[current.pairs - 1 - i])
                for i in range(current.pairs)
            )
        )
        mask_words.append(tuple(f.scalar(DecimalPairBand.GT_HIGH) for f in frame))
        xor_words.append(tuple(f.scalar(TemporalBankChannel.CARRY_XOR) for f in frame))
        odd_words.append(odd_boundary_pairs(current, inlet))
        current = next_state
        steps += 1
    if period % len(inlet_motif):
        raise AssertionError("model return lost its inward clock")
    # The complete source state and input phase return. Primitive periods
    # of the emitted raw digits and Boolean masks are *future*-closed for
    # this declared conditional model, though possibly smaller.
    raw = _measured_period(tuple(pair_words[entry:steps]), ledger)
    gt = _measured_period(tuple(mask_words[entry:steps]), ledger)
    xor = _measured_period(tuple(xor_words[entry:steps]), ledger)
    complete = all(word is not None for word in odd_words[entry:steps])
    p_pair: int | None = None
    p_gt: int | None = None
    p_xor: int | None = None
    if complete:
        physical: list[tuple[tuple[int, int], ...]] = []
        for j in range(entry, steps):
            odd_word = odd_words[j]
            if odd_word is None:
                raise AssertionError("conditional intermediate digit is not canonical")
            physical.extend((pair_words[j], odd_word))
        p_pair = _measured_period(tuple(physical), ledger)
        p_gt = _measured_period(
            tuple(tuple(int(a + b >= 15) for a, b in word) for word in physical),
            ledger,
        )
        p_xor = _measured_period(
            tuple(
                tuple(int((a >= 5) != (b >= 5)) for a, b in word) for word in physical
            ),
            ledger,
        )
    return _ConditionalBirthModel(
        tuple(states),
        tuple(frames),
        ConditionalBirthReturn(
            len(inlet_motif),
            entry,
            period,
            raw,
            gt,
            xor,
            period // len(inlet_motif),
            steps,
            p_pair,
            p_gt,
            p_xor,
        ),
    )


def conditional_birth_return(
    state: BirthRingState,
    inlet_motif: tuple[BirthRingPorts, ...],
    *,
    max_states: int = MAX_BIRTH_CONDITIONAL_STATES,
) -> ConditionalBirthReturn:
    """Compute the minimal period in a declared periodic-inlet model."""
    return _enumerate_conditional_birth_model(
        state,
        inlet_motif,
        max_states=max_states,
    ).result


def power_birth_model(
    state: BirthRingState,
    inlet_motif: tuple[BirthRingPorts, ...],
    steps: int,
    *,
    max_states: int = MAX_BIRTH_CONDITIONAL_STATES,
) -> tuple[BirthRingState, tuple[PeriodicBankFrame, ...], ConditionalBirthReturn]:
    """Produce any conditional-model frame without chronological replay.

    The inlet motif is an *assumption* unless the caller holds a separate
    authenticated source/horizon certificate for its repetition.
    """
    steps = validate_birth_duration(steps)
    model = _enumerate_conditional_birth_model(
        state, inlet_motif, max_states=max_states
    )
    end_state, frame = model.at(steps)
    return end_state, frame, model.result


@dataclass(frozen=True, slots=True)
class BirthLayerPeriod:
    pairs: int
    witnessed_preperiod: int | None
    witnessed_inlet_period: int | None
    conditional_return: ConditionalBirthReturn | None
    source_finite_horizon_verified: bool
    indefinite_source_authorized: bool
    status: str
    diagonal_induction: FiniteInductionWitness | None = None


@dataclass(frozen=True, slots=True)
class CertifiedBirthRing(SourceAuthorizedRecord):
    """A completely source-sealed finite ring of *moving* boundary pairs."""

    source_generation: int
    source_width: int
    source_phase: int
    f_steps: int
    pairs: int
    clock: CertifiedBirthClock
    final_pairs: tuple[PeriodicBankFrame, ...]
    layers: tuple[BirthLayerPeriod, ...]
    outermost_pair_return: ClosedBorderPairReturn | None

    @property
    def independently_powered_pairs(self) -> int:
        return max(
            (v.pairs for v in self.layers if v.source_finite_horizon_verified),
            default=0,
        )

    def validated_projection(self) -> dict[str, object]:
        """Return a JSON-shaped snapshot after checking source authority."""
        validate_source_record(self)
        layer_packets: list[dict[str, object]] = []
        for layer in self.layers:
            action = layer.conditional_return
            layer_packets.append(
                {
                    "pairs": layer.pairs,
                    "witnessed_preperiod": layer.witnessed_preperiod,
                    "witnessed_inlet_period": layer.witnessed_inlet_period,
                    "conditional_return": None if action is None else asdict(action),
                    "ordered_pair_period_physical": (
                        None if action is None else action.physical_pair_period
                    ),
                    "source_finite_horizon_verified": (
                        layer.source_finite_horizon_verified
                    ),
                    "indefinite_source_authorized": False,
                    "status": layer.status,
                    "diagonal_induction": (
                        None
                        if layer.diagonal_induction is None
                        else asdict(layer.diagonal_induction)
                    ),
                }
            )
        return {
            "source_generation": self.source_generation,
            "source_width": self.source_width,
            "source_phase": self.source_phase,
            "f_steps": self.f_steps,
            "pairs": self.pairs,
            "clock": asdict(self.clock),
            "final_pairs": [asdict(frame) for frame in self.final_pairs],
            "layers": layer_packets,
            "outermost_pair_return": (
                None
                if self.outermost_pair_return is None
                else asdict(self.outermost_pair_return)
            ),
            "seam_response_classes_by_phase": (2, 4, 2, 1),
            "independently_powered_pairs": self.independently_powered_pairs,
            "indefinite_source_authorized": False,
        }


def certified_birth_ring(
    source: PointedBankSource,
    *,
    pairs: int,
    max_model_states: int = 1024,
) -> CertifiedBirthRing:
    """Run the finite birth publisher under an aggregate scratch reservation."""
    source.validate(require_issued_cursor=True)
    if (
        type(pairs) is not int
        or not 1 <= pairs <= MAX_BIRTH_LAYER_PAIRS
        or type(max_model_states) is not int
        or not 1 <= max_model_states <= MAX_BIRTH_CONDITIONAL_STATES
    ):
        raise ValueError("invalid birth-ring model budget")
    horizon = source.f_steps
    if not 1 <= horizon <= MAX_BIRTH_LAYER_HORIZON:
        raise ValueError("birth-layer horizon must be between 1 and 160 F-steps")
    available_pairs = (source.width_in - 2) // 2
    if available_pairs < pairs:
        raise ValueError(
            "birth-ring source is too narrow for the requested disjoint pairs"
        )
    units = _birth_strip_workspace_units(pairs, horizon) + (
        _birth_model_workspace_units(pairs, max_model_states)
    )
    if units > MAX_BIRTH_TEMPORARY_UNITS:
        raise ValueError("birth-ring request exceeds its aggregate workspace cap")
    with source.ledger.reservation(source.scratch_owner, entries=units, nodes=units):
        record = _certified_birth_ring_reserved(
            source, pairs=pairs, max_model_states=max_model_states
        )
    source.ledger.bump(metric_keys.DOUBLE_REVERSE_BIRTH_LAYER_PUBLICATIONS)
    return record


def _certified_birth_ring_reserved(
    source: PointedBankSource,
    *,
    pairs: int,
    max_model_states: int,
) -> CertifiedBirthRing:
    """Build exact moving-boundary layers over an owner-issued finite horizon.

    Only the two newly exposed inward digits are read from source cones at
    each F tick.  The K-pair state is advanced by the exact local stencil;
    one authenticated powered endpoint grammar checks the resulting strip.
    A finite repeated inlet may drive a conditional lasso only through the
    witnessed horizon and never authorizes an infinite source continuation.
    """
    # This helper is called only after certified_birth_ring has checked the
    # source, request bounds, and aggregate reservation.
    engine = source.engine
    horizon = source.f_steps
    k = pairs
    if type(k) is not int or k < 1:
        raise ValueError("birth ring requires at least one boundary pair")
    arena = source.arena
    root = source.root
    phase_in = source.phase
    width_in = source.width_in
    source_generation = source.physical_prefix
    if source.width_bits(width_in) > source.max_state_bits:
        raise ValueError("birth ring source exceeds its state-bit budget")
    initial = BirthRingState(
        tuple(symbol_at(arena, root, i) for i in range(k)),
        tuple(symbol_at(arena, root, width_in - k + i) for i in range(k)),
        phase_in,
    )
    states: dict[int, list[BirthRingState]] = {depth: [] for depth in range(1, k + 1)}
    ports: dict[int, list[BirthRingPorts]] = {depth: [] for depth in range(1, k + 1)}
    current = initial
    for t in range(horizon + 1):
        l_births, r_births = growth_ports(phase_in, t)
        width = width_in + l_births + r_births
        if source.width_bits(width) > source.max_state_bits:
            raise ValueError("birth ring endpoint exceeds its state-bit budget")
        phase = (phase_in + 2 * t) % 4
        if current.phase != phase:
            raise AssertionError("moving-boundary phase drifted from its birth clock")
        positions = (k, width - k - 1)
        inlet_digits: list[int] = []
        for pos in positions:
            if not 0 <= pos < width:
                raise ValueError("birth ring requested an out-of-width source digit")
            digit = (
                symbol_at(arena, root, pos)
                if t == 0
                else engine.pointed_stencil(root, t, phase_in, pos).digit
            )
            inlet_digits.append(digit)
            source.ledger.bump(metric_keys.DOUBLE_REVERSE_BIRTH_LAYER_SOURCE_PORT_READS)
        inlet = BirthRingPorts(*inlet_digits)
        state, layer_inlet = current, inlet
        for depth in range(k, 0, -1):
            if depth == k:
                state, layer_inlet = current, inlet
            else:
                state, layer_inlet = project_birth_layer(state)
            states[depth].append(state)
            ports[depth].append(layer_inlet)
        if t < horizon:
            source.ledger.bump(metric_keys.DOUBLE_REVERSE_BIRTH_LAYER_STRIP_STEPS)
            current, _ = current.advance(inlet)

    endpoint_action = engine.advance_action(root, horizon, phase_in)
    engine.validate_action(endpoint_action)
    endpoint_root = engine.root_of(endpoint_action.target)
    endpoint_width = arena.nodes[endpoint_root].length
    endpoint_state = states[k][horizon]
    if endpoint_width != width_in + sum(growth_ports(phase_in, horizon)):
        raise AssertionError("powered birth-ring endpoint has an inexact width")
    if endpoint_state.left != tuple(
        symbol_at(arena, endpoint_root, i) for i in range(k)
    ) or endpoint_state.right != tuple(
        symbol_at(arena, endpoint_root, endpoint_width - k + i) for i in range(k)
    ):
        raise AssertionError("powered birth layers disagree with the admitted endpoint")
    final_frames = endpoint_state.advance(ports[k][horizon])[1]
    layers: list[BirthLayerPeriod] = []
    for depth in range(k, 0, -1):
        word = tuple(ports[depth])
        witness, comparisons = finite_suffix_period(word)
        _charge_period_comparisons(source.ledger, comparisons)
        if witness is None:
            layers.append(
                BirthLayerPeriod(
                    depth, None, None, None, False, False, "no_certified_inlet_period"
                )
            )
            continue
        start, period = witness
        motif = word[start : start + period]
        try:
            model_action = _enumerate_conditional_birth_model(
                states[depth][start],
                motif,
                max_states=max_model_states,
                ledger=source.ledger,
            )
        except BirthReturnBudgetExceeded:
            layers.append(
                BirthLayerPeriod(
                    depth,
                    start,
                    period,
                    None,
                    False,
                    False,
                    "conditional_return_exceeds_budget",
                )
            )
            continue
        # A source-sealed finite word admits the conditional model ONLY on
        # [start, D]. Use the model's powered class to issue the actual
        # output, then compare with the independently certified source cone.
        powered_state, powered_frame = model_action.at(horizon - start)
        expected = states[depth][horizon]
        verified = expected.advance(ports[depth][horizon])[1]
        if powered_state != expected or powered_frame != verified:
            raise AssertionError("powered birth-ring quotient changed a source digit")
        model = model_action.result
        induction_start = start + model.preperiod
        induction = (
            finite_birth_period_induction(
                tuple(states[depth]),
                tuple(ports[depth]),
                lag_fsteps=model.ordered_pair_period,
                start_fstep=induction_start,
                ledger=source.ledger,
            )
            if induction_start + model.ordered_pair_period < horizon
            else None
        )
        layers.append(
            BirthLayerPeriod(
                depth,
                start,
                period,
                model,
                True,
                False,
                "finite_source_conditional_return",
                induction,
            )
        )
    clock = birth_clock_for_source(source)
    border_edge = (
        symbol_at(arena, root, 0),
        symbol_at(arena, root, 1),
        symbol_at(arena, root, width_in - 2),
        symbol_at(arena, root, width_in - 1),
    )
    try:
        border_period = certified_closed_outer_pair_return(border_edge)
    except ValueError:
        # Other admitted cylinders can be observed finitely, but do not get
        # the separate indefinite first-pair SCC theorem.
        border_period = None
    return issue_source_record(
        CertifiedBirthRing(
            source_generation,
            width_in,
            phase_in,
            horizon,
            k,
            clock,
            final_frames,
            tuple(layers),
            border_period,
        ),
        arena,
        root,
        source_generation=source_generation,
    )


__all__ = [
    "BirthLayerPeriod",
    "BirthReturnBudgetExceeded",
    "BirthRingPorts",
    "BirthRingState",
    "CertifiedBirthRing",
    "ConditionalBirthReturn",
    "FiniteInductionWitness",
    "assert_birth_layer_step",
    "birth_clock_for_source",
    "certified_birth_ring",
    "conditional_birth_return",
    "odd_boundary_pairs",
    "power_birth_model",
    "project_birth_layer",
]
