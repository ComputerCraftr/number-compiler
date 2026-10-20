"""Source-authorized *open*, two-sided 2rev10 temporal bank.

Unlike the spatially wrapped finite ring, this action receives the actual
neighbour digits at each step. The neighbour stream is certified from the
original source's finite causal cones, never guessed from a 12/24/576 phase.
The right ray is shifted by the *difference* of the two border births.

A periodic input stream can drive a finite Moore-minimized deterministic
ring. The periodic claim is valid ONLY for the source-certified finite horizon;
a periodic model is not an infinite certificate for the underlying integer.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys

from ._temporal_bank_authority import (
    issue_source_record,
    validate_source_record,
)
from .protected_temporal_bank import (
    BANK_CHANNELS,
    BankChannel,
    PeriodicBankFrame,
    SourceAuthorizedFrameWindow,
    bank_channel_name,
    parse_bank_channel,
)
from .stencil_moore import stencil_cell
from .temporal_bank_output_morphism import frame_from_digits
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource

# The finite input certificate is bounded: this is not an unconstrained
# reconstruction of a large intermediate integer or an infinite oracle tape.
MAX_OPEN_HORIZON = 32
MAX_OPEN_PAIRS = 16
MAX_OPEN_MOORE_STATES = 4096
OpenOutputWord = tuple[tuple[int, ...], int, tuple[int, ...]]


class OpenTemporalRingRefused(UncertifiedPointedStencilError):
    """The bounded source does not authorize this open-ring projection."""


@dataclass(frozen=True, slots=True)
class OpenRingPorts:
    """At the present CA time: 1 left neighbour at each end, 2 right ones.

    The two extra right neighbours are necessary for a skew shift of +/-1;
    reusing a single neighbour there silently loses a digit on grow steps.
    Right neighbours and right word are in ordinary MSDF spatial order.
    """

    left_outer: int
    left_inner: int
    right_before: tuple[int, int]
    right_after: tuple[int, int]

    def __post_init__(self) -> None:
        if (
            type(self.right_before) is not tuple
            or type(self.right_after) is not tuple
            or len(self.right_before) != 2
            or len(self.right_after) != 2
        ):
            raise ValueError("skewed right ray requires immutable two-cell ports")
        digits = (
            self.left_outer,
            self.left_inner,
            *self.right_before,
            *self.right_after,
        )
        if any(type(value) is not int or not 0 <= value <= 9 for value in digits):
            raise ValueError("open temporal ports require six decimal digits")


@dataclass(frozen=True, slots=True)
class OpenRingState:
    """Two moving, disjoint physical CA strips; never wrap either strip."""

    left: tuple[int, ...]
    right: tuple[int, ...]
    phase: int

    def __post_init__(self) -> None:
        if (
            type(self.left) is not tuple
            or type(self.right) is not tuple
            or not self.left
            or len(self.left) != len(self.right)
            or type(self.phase) is not int
            or self.phase not in (0, 1, 2, 3)
            or any(
                type(d) is not int or not 0 <= d <= 9 for d in self.left + self.right
            )
        ):
            raise ValueError("invalid open two-sided bank state")

    @property
    def pairs(self) -> int:
        return len(self.left)

    def advance(
        self, ports: OpenRingPorts
    ) -> tuple[OpenRingState, tuple[PeriodicBankFrame, ...]]:
        """Exact F=T**2 transfer, with the width-clock's reflected skew."""
        n = len(self.left)
        left_halo = (ports.left_outer, *self.left, ports.left_inner)
        new_left = tuple(stencil_cell(*left_halo[i : i + 3]) for i in range(n))
        before_right = (*ports.right_before, *self.right, *ports.right_after)
        birth_left, birth_right = growth_ports(self.phase, 1)
        skew = birth_right - birth_left
        # before_right[2+i] is the old centre of right[i]; the new
        # source-relative ray is one site left/right according to skew.
        new_right = tuple(
            stencil_cell(*before_right[i + 1 + skew : i + 4 + skew]) for i in range(n)
        )
        future = OpenRingState(new_left, new_right, (self.phase + 2) % 4)
        frames = tuple(
            frame_from_digits(
                (self.left[i], self.right[n - 1 - i]),
                (new_left[i], new_right[n - 1 - i]),
                birth_left,
                birth_right,
            )
            for i in range(n)
        )
        return future, frames


@dataclass(frozen=True, slots=True)
class CertifiedOpenTemporalBank(SourceAuthorizedFrameWindow):
    """Exact finite-horizon bank with source-bound input/carry witnesses.

    A temporal Moore class is supplied only if the certified ingress word
    repeats AND its input-driven finite-state orbit closes. A class is never
    an authorization to extend the certified horizon.
    """

    physical_prefix: int
    phase_in: int
    f_steps: int
    width_in: int
    width_out: int
    final_pair_start: int
    frames: tuple[PeriodicBankFrame, ...]
    input_ports: tuple[OpenRingPorts, ...]
    input_period: int | None
    moore_classes: int | None
    moore_preperiod: int | None
    moore_cycle: int | None
    initial_state: OpenRingState

    def counts(self) -> dict[str, int]:
        validate_source_record(self)
        return {
            bank_channel_name(channel): sum(f.scalar(channel) for f in self.frames)
            for channel in BANK_CHANNELS
        }

    def validated_projection(
        self, channels: tuple[str | BankChannel, ...]
    ) -> tuple[dict[str, int], dict[str, OpenOutputWord]]:
        """Return counts and selected words after one source-authority check.

        This is the packet boundary for callers that need several projections
        from the same immutable, source-issued bank. Individual public accessors
        remain independently validating.
        """
        if type(channels) is not tuple or len(channels) > len(BANK_CHANNELS):
            raise ValueError("open temporal projection has invalid channels")
        selected = tuple(parse_bank_channel(channel) for channel in channels)
        if len(set(selected)) != len(selected):
            raise ValueError("open temporal projection has duplicate channels")
        validate_source_record(self)
        totals = {bank_channel_name(channel): 0 for channel in BANK_CHANNELS}
        words: dict[str, list[int]] = {
            bank_channel_name(channel): [] for channel in selected
        }
        selected_set = set(selected)
        for frame in self.frames:
            for channel in BANK_CHANNELS:
                value = frame.scalar(channel)
                wire_name = bank_channel_name(channel)
                totals[wire_name] += value
                if channel in selected_set:
                    words[wire_name].append(value)
        return totals, {
            channel: (tuple(values), 1, ()) for channel, values in words.items()
        }

    def output_word(
        self, channel: str | BankChannel
    ) -> tuple[tuple[int, ...], int, tuple[int, ...]]:
        validate_source_record(self)
        selected = parse_bank_channel(channel)
        return (tuple(f.scalar(selected) for f in self.frames), 1, ())


def _minimal_certified_period(ports: tuple[OpenRingPorts, ...]) -> int | None:
    """An exact *finite* ingress motif, not an infinite input oracle."""
    # At least two copies are required: a one-off prefix is not a pump.
    n = len(ports)
    for p in range(1, n // 2 + 1):
        if all(port == ports[i % p] for i, port in enumerate(ports)):
            return p
    return None


def closed_driven_moore(
    initial: OpenRingState,
    motif: tuple[OpenRingPorts, ...],
    target_time: int,
) -> tuple[tuple[PeriodicBankFrame, ...], int, int, int] | None:
    """Power the complete-future input-driven Moore action for proved inlets.

    The admitted input alphabet is one source-certified letter per clock
    phase. The same minimizer also supports multiple conditional letters;
    other input words cannot inherit this certificate without a new issuer.
    """
    from .conditional_open_moore import (
        ConditionalOpenMooreBudgetExceeded,
        minimize_conditional_open_ring,
    )

    try:
        moore = minimize_conditional_open_ring(
            initial,
            tuple((port,) for port in motif),
            max_states=MAX_OPEN_MOORE_STATES,
        )
    except ConditionalOpenMooreBudgetExceeded:
        return None
    # Advance the *minimized class*, not the full state orbit. The next input
    # port was independently authenticated from the same source lightcones.
    quotient_target = (
        moore.word(motif)
        .power(target_time // len(motif))
        .then(moore.word(motif[: target_time % len(motif)]))
    )
    klass = quotient_target.targets[moore.initial_class]
    if klass is None:
        raise AssertionError("source-authenticated inlet word was refused")
    letter_index = moore.alphabet.index(motif[target_time % len(motif)])
    frames = moore.emissions[klass][letter_index]
    if frames is None:
        raise AssertionError("minimized ring lost its admitted output letter")

    # This is the deterministic control's genuine cycle, not a period
    # inferred from the target value or from the 576-step training corpus.
    # A Moore class by itself is not a temporal clock. The same class at
    # different positions of a nonconstant inlet motif has a different next
    # input letter. Detect cycles on the product (class, inlet phase).
    seen = {(moore.initial_class, 0): 0}
    current = moore.initial_class
    clock = 0
    while True:
        port_index = moore.alphabet.index(motif[clock % len(motif)])
        next_class = moore.transitions[current][port_index]
        if next_class is None:
            raise AssertionError(
                "certified temporal driver reached a rejected transition"
            )
        clock += 1
        next_key = (next_class, clock % len(motif))
        if next_key in seen:
            return frames, moore.class_count, seen[next_key], clock - seen[next_key]
        seen[next_key] = clock
        current = next_class
        if clock > moore.class_count * len(motif):
            raise AssertionError("conditional Moore source clock failed to close")


def certified_open_temporal_bank(
    source: PointedBankSource,
    final_pair_start: int,
    pair_count: int,
) -> CertifiedOpenTemporalBank:
    """Build a finite, guarded, source-derived open-ring temporal bank action.

    All ingress digits come from exact *source* causal cones; the endpoint
    integer/root is not built or consulted. No intermediate integer is
    chronologically advanced. The input guard itself costs O(D) pointed cone
    requests, so it does NOT prove fast unbounded powering on seed 196.
    """
    d = source.f_steps
    if (
        type(d) is not int
        or d < 1
        or type(pair_count) is not int
        or pair_count < 1
        or type(final_pair_start) is not int
        or final_pair_start < 0
    ):
        raise ValueError("open ring exceeds its certified finite-horizon budget")
    source.validate(require_issued_cursor=True)
    if d > MAX_OPEN_HORIZON or pair_count > MAX_OPEN_PAIRS:
        _refuse_open_ring(
            source, "open ring exceeds its certified finite-horizon budget"
        )
    if source.max_steps < source.physical_prefix + 2 * (d + 1):
        _refuse_open_ring(source, "open ring exceeds the admitted physical-step budget")
    width = source.width_in
    births_l, births_r = growth_ports(source.phase, d)
    next_births_l, next_births_r = growth_ports(source.phase, d + 1)
    width_out = width + births_l + births_r
    next_width = width + next_births_l + next_births_r
    if (
        2 * (final_pair_start + pair_count - 1) >= width_out - 1
        or 2 * (final_pair_start + (next_births_l - births_l) + pair_count - 1)
        >= next_width - 1
    ):
        _refuse_open_ring(source, "open ring crosses the moving symmetric center")
    pair_start = final_pair_start - births_l
    right_start = width - pair_start - pair_count

    # Negative coordinates are genuine zero-extended CA cells. They become
    # nonzero on a birth step; refusing them would exclude precisely the
    # new leading/trailing digits whose carries the border macro certifies.
    def original_digit(index: int) -> int:
        return symbol_at(source.arena, source.root, index) if 0 <= index < width else 0

    initial = OpenRingState(
        tuple(original_digit(i) for i in range(pair_start, pair_start + pair_count)),
        tuple(original_digit(i) for i in range(right_start, right_start + pair_count)),
        source.phase,
    )
    # Sample F**t on an original-source coordinate by exact CA cones. The
    # canonical final index is translated by the certified left-birth clock.
    sampled: dict[tuple[int, int], int] = {}

    def source_cell(t: int, coordinate: int) -> int:
        key = (t, coordinate)
        if key in sampled:
            return sampled[key]
        left, right = growth_ports(source.phase, t)
        output_index = coordinate + left
        present_width = width + left + right
        if source.width_bits(present_width) > source.max_state_bits:
            _refuse_open_ring(
                source, "open temporal ring exceeds its authenticated state budget"
            )
        if not 0 <= output_index < present_width:
            digit = 0
        elif t == 0:
            digit = symbol_at(source.arena, source.root, output_index)
        else:
            digit = source.engine.pointed_stencil(
                source.root, t, source.phase, output_index
            ).digit
        sampled[key] = digit
        return digit

    ports: list[OpenRingPorts] = []
    for t in range(d + 1):
        left_growth, right_growth = growth_ports(source.phase, t)
        skew = right_growth - left_growth
        right = right_start + skew
        ports.append(
            OpenRingPorts(
                source_cell(t, pair_start - 1),
                source_cell(t, pair_start + pair_count),
                (source_cell(t, right - 2), source_cell(t, right - 1)),
                (
                    source_cell(t, right + pair_count),
                    source_cell(t, right + pair_count + 1),
                ),
            )
        )
    state = initial
    at_target: OpenRingState | None = None
    following: OpenRingState | None = None
    emitted: tuple[PeriodicBankFrame, ...] = ()
    for t, port in enumerate(ports):
        if t == d:
            at_target = state
        state, emitted = state.advance(port)
        if t == d:
            following = state
    if at_target is None or following is None:
        raise AssertionError(
            "open ring failed to complete the source-certified horizon"
        )
    # Arithmetic from the source's exact causal lightcones checks the final
    # ring without materializing the global target; these are already part
    # of the issuer's source-derived boundary proof.
    for j in range(pair_count):
        x_left = pair_start + j
        x_right = width - 1 - pair_start - j + (births_r - births_l)
        if at_target.left[j] != source_cell(d, x_left) or at_target.right[
            pair_count - 1 - j
        ] != source_cell(d, x_right):
            raise AssertionError(
                "open temporal bank mismatches its source-cone witness"
            )
    source.ledger.bump(
        _double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_SOURCE_PORTS, len(ports)
    )
    candidate_p = _minimal_certified_period(tuple(ports))
    moore_count: int | None = None
    preperiod: int | None = None
    cycle: int | None = None
    if candidate_p is not None:
        quotient = closed_driven_moore(initial, tuple(ports[:candidate_p]), d)
        if quotient is not None:
            frames, moore_count, preperiod, cycle = quotient
            if frames != emitted:
                raise AssertionError(
                    "Moore quotient changed the verified source output"
                )
            source.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_MOORE_PUBLICATIONS
            )
    result = CertifiedOpenTemporalBank(
        source.physical_prefix,
        source.phase,
        d,
        width,
        width_out,
        final_pair_start,
        emitted,
        tuple(ports),
        candidate_p if moore_count is not None else None,
        moore_count,
        preperiod,
        cycle,
        initial,
    )
    return issue_source_record(
        result, source.arena, source.root, source_generation=source.physical_prefix
    )


def _refuse_open_ring(source: PointedBankSource, reason: str) -> None:
    source.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_GUARD_REFUSALS)
    raise OpenTemporalRingRefused(reason)


__all__ = [
    "CertifiedOpenTemporalBank",
    "OpenOutputWord",
    "OpenRingPorts",
    "OpenRingState",
    "OpenTemporalRingRefused",
    "certified_open_temporal_bank",
]
