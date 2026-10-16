"""Temporally Moore-minimized, source-guarded ``2rev10`` border ports.

This is a *temporal* Mealy quotient, not the local ten-digit stencil quotient.
Each state is an entire two-sided border `(MSD, second, penultimate, LSD)`;
each input is the *unknown inward multiplication carry* supplied by the
interior.  Outputs include the two symmetric GT-high bands, decimal doubling
carries, reflected carry XOR, and the two low borrow bits of the **raw**
innovation ``reverse(T(X))-reverse(X)``.

The nine-state nonshrinking border cylinder is closed for BOTH ingress bits.
Moore refinement uses the complete future response for either input.  Powering
with unknown ingress computes an exact envelope over an overapproximation of
actual decimal trajectories; only singleton outputs/extrema are publishable
as exact observations.  No guessed periodic input tape is ever authorized.
"""

from __future__ import annotations

from contextlib import nullcontext
from dataclasses import dataclass
from typing import Literal, TypeAlias, cast

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)

from .boundary_cycles import CANDIDATE_COMPONENTS, Edge, boundary_steps

TemporalObserver: TypeAlias = Literal[
    "gt_high",
    "carry_edge",
    "reflected_xor",
    "raw_borrow",
    "innovation_xor",
    "growth",
    "joint",
]

EDGE_STATES: tuple[Edge, ...] = tuple(sorted(CANDIDATE_COMPONENTS[0]))
_EDGE_IDS = {state: i for i, state in enumerate(EDGE_STATES)}
OBSERVERS: tuple[TemporalObserver, ...] = (
    "gt_high",
    "carry_edge",
    "reflected_xor",
    "raw_borrow",
    "innovation_xor",
    "growth",
    "joint",
)


def _edge_mask(edge: Edge) -> tuple[int, int, int]:
    a, b, y, z = edge
    gt_high = int(a + z >= 15) | (int(b + y >= 15) << 1)
    # Physical T scans the original word MSDF and each outgoing carry
    # is precisely [digit >= 5].  The external four cells are distinct.
    carry = sum(int(d >= 5) << i for i, d in enumerate(edge))
    reflected_xor = int((a >= 5) != (z >= 5)) | (int((b >= 5) != (y >= 5)) << 1)
    return gt_high, carry, reflected_xor


def _raw_borrow_low2(source: Edge, target: Edge) -> int:
    """Two LSD-first borrows of rev(target)-rev(source), no sign swap.

    Reversal makes the first and second MSD digits the low decimal cells of
    its integer.  Unknown deeper digits cannot alter these outgoing borrows.
    Width growth adds only more high decimal cells, not these low two.
    """
    borrow = 0
    mask = 0
    for i in range(2):
        borrow = int(target[i] < source[i] + borrow)
        mask |= borrow << i
    return mask


def _step(
    edge: Edge, ingress: int, *, ledger: ResourceLedger | None = None
) -> tuple[Edge, int]:
    if edge not in _EDGE_IDS:
        raise ValueError("temporal bank requires a certified nine-state cylinder")
    if type(ingress) is not int or ingress not in (0, 1):
        raise ValueError("inward carry must be one exact Boolean")
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_TRANSITION_EVALUATIONS
        )
    relation = boundary_steps(edge)
    if relation.shrinking_frontier:
        raise AssertionError("certified cylinder entered a shrinking frontier")
    matches = [
        step
        for step in relation.steps
        if step.inward_carry is None or step.inward_carry == ingress
    ]
    if len(matches) != 1 or matches[0].target not in _EDGE_IDS:
        raise AssertionError("temporal cylinder is not ingress-closed")
    return matches[0].target, matches[0].width_delta


def _output(
    edge: Edge,
    ingress: int,
    observer: TemporalObserver,
    *,
    transition: tuple[Edge, int] | None = None,
    ledger: ResourceLedger | None = None,
) -> tuple[int, ...]:
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_OUTPUT_EVALUATIONS
        )
    target, growth = (
        _step(edge, ingress, ledger=ledger) if transition is None else transition
    )
    gt_high, carry, rxor = _edge_mask(edge)
    borrow = _raw_borrow_low2(edge, target)
    # The innovation low cells are the first (MSDF) carry columns.
    innovation_xor = (carry & 3) ^ borrow
    if observer == "gt_high":
        return (gt_high,)
    if observer == "carry_edge":
        return (carry,)
    if observer == "reflected_xor":
        return (rxor,)
    if observer == "raw_borrow":
        return (borrow,)
    if observer == "innovation_xor":
        return (innovation_xor,)
    if observer == "growth":
        return (growth,)
    if observer == "joint":
        return (gt_high, carry, rxor, borrow, innovation_xor, growth)
    raise ValueError("unknown temporal border observer")


def _classes(
    signatures: list[object], *, ledger: ResourceLedger | None = None
) -> tuple[int, ...]:
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
            len(signatures),
        )
    ids: dict[object, int] = {}
    return tuple(ids.setdefault(value, len(ids)) for value in signatures)


@dataclass(frozen=True, slots=True)
class TemporalBorderMoore:
    """Coarsest complete-future, ingress-driven Mealy quotient on the cylinder."""

    observer: TemporalObserver
    classes: tuple[int, ...]
    initial_class_count: int
    rounds: int
    transitions: tuple[tuple[int, int], ...]
    emissions: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]

    @property
    def state_count(self) -> int:
        return len(self.transitions)

    def class_of(self, edge: Edge) -> int:
        try:
            return self.classes[_EDGE_IDS[edge]]
        except KeyError as error:
            raise ValueError("edge has no certified temporal class") from error


def minimize_temporal_border(
    observer: TemporalObserver, *, ledger: ResourceLedger | None = None
) -> TemporalBorderMoore:
    """Future-refine all *time* transitions, retaining ingress and emissions.

    This is not an unguarded whole-word quotient: its universe is exactly the
    nine-state, all-ingress-closed edge cylinder, and its output contract names
    which ports may be published under the quotient.
    """
    if observer not in OBSERVERS:
        raise ValueError("unknown temporal observer")
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_CONSTRUCTIONS
        )
    transition_rows = tuple(
        tuple(_step(edge, ingress, ledger=ledger) for ingress in (0, 1))
        for edge in EDGE_STATES
    )
    emissions_raw = tuple(
        (
            _output(
                edge,
                0,
                observer,
                transition=transition_rows[index][0],
                ledger=ledger,
            ),
            _output(
                edge,
                1,
                observer,
                transition=transition_rows[index][1],
                ledger=ledger,
            ),
        )
        for index, edge in enumerate(EDGE_STATES)
    )
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
            len(transition_rows),
        )
    targets_raw = tuple(
        tuple(_EDGE_IDS[transition[0]] for transition in row) for row in transition_rows
    )
    classes = _classes(list(emissions_raw), ledger=ledger)
    initial_count = len(set(classes))
    rounds = 0
    while True:
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_REFINEMENT_SWEEPS
            )
        future = _classes(
            [
                (classes[i], *(classes[successor] for successor in targets_raw[i]))
                for i in range(len(EDGE_STATES))
            ],
            ledger=ledger,
        )
        if future == classes:
            break
        classes = future
        rounds += 1
        if ledger is not None:
            ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_REFINEMENT_ROUNDS
            )
        if rounds >= len(EDGE_STATES):
            raise AssertionError("temporal Moore refinement failed to stabilize")
    count = len(set(classes))
    class_rep: list[int] = [-1] * count
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
            len(classes),
        )
    for index, klass in enumerate(classes):
        if class_rep[klass] == -1:
            class_rep[klass] = index
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
            len(class_rep),
        )
    transitions = tuple(
        (classes[targets_raw[index][0]], classes[targets_raw[index][1]])
        for index in class_rep
    )
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
            len(class_rep),
        )
    emissions = tuple(emissions_raw[index] for index in class_rep)
    # Check that partitioning did not silently discard an output or successor.
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
            len(classes),
        )
    for i, klass in enumerate(classes):
        if (
            tuple(classes[next_id] for next_id in targets_raw[i]) != transitions[klass]
            or emissions_raw[i] != emissions[klass]
        ):
            raise AssertionError("temporal Moore classes are not successor closed")
    return TemporalBorderMoore(
        observer, classes, initial_count, rounds, transitions, emissions
    )


@dataclass(frozen=True, slots=True)
class TemporalBorderEnvelope:
    """Outputs forced or allowed over every abstract inward-carry history."""

    observer: TemporalObserver
    initial_edge: Edge
    steps: int
    initial_classes: int
    moore_classes: int
    refinement_rounds: int
    possible_next_outputs: tuple[tuple[int, ...], ...]
    minimum_emission_sum: int
    maximum_emission_sum: int
    possible_end_classes: tuple[int, ...]

    @property
    def exact_sum(self) -> int | None:
        if self.minimum_emission_sum == self.maximum_emission_sum:
            return self.minimum_emission_sum
        return None

    @property
    def forced_next_output(self) -> tuple[int, ...] | None:
        if len(self.possible_next_outputs) == 1:
            return self.possible_next_outputs[0]
        return None


_Matrix: TypeAlias = tuple[tuple[int | None, ...], ...]


def _compose_cost(
    a: _Matrix,
    b: _Matrix,
    *,
    maximum: bool,
    ledger: ResourceLedger | None,
) -> _Matrix:
    n = len(a)
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MATRIX_COMPOSITIONS
        )
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MATRIX_CELLS, n * n * n
        )
    rows: list[tuple[int | None, ...]] = []
    for i in range(n):
        out: list[int | None] = []
        for j in range(n):
            values = []
            for k in range(n):
                before, after = a[i][k], b[k][j]
                if before is not None and after is not None:
                    values.append(before + after)
            out.append((max(values) if maximum else min(values)) if values else None)
        rows.append(tuple(out))
    return tuple(rows)


def _powered_envelope(
    moore: TemporalBorderMoore,
    edge: Edge,
    steps: int,
    *,
    ledger: ResourceLedger | None,
) -> TemporalBorderEnvelope:
    if type(steps) is not int or steps < 0:
        raise ValueError("temporal border duration must be nonnegative")
    if moore.observer == "joint":
        raise ValueError("joint bank is a temporal equality contract, not a scalar sum")
    n = moore.state_count
    min_rows: list[list[int | None]] = [[None] * n for _ in range(n)]
    max_rows: list[list[int | None]] = [[None] * n for _ in range(n)]
    for state in range(n):
        for ingress in (0, 1):
            target = moore.transitions[state][ingress]
            value = moore.emissions[state][ingress][0]
            prev_min, prev_max = min_rows[state][target], max_rows[state][target]
            min_rows[state][target] = (
                value if prev_min is None else min(prev_min, value)
            )
            max_rows[state][target] = (
                value if prev_max is None else max(prev_max, value)
            )
    base_min: _Matrix = tuple(tuple(row) for row in min_rows)
    base_max: _Matrix = tuple(tuple(row) for row in max_rows)
    identity: _Matrix = tuple(
        tuple(0 if i == j else None for j in range(n)) for i in range(n)
    )
    total_min, total_max = identity, identity
    remaining = steps
    while remaining:
        if remaining & 1:
            total_min = _compose_cost(total_min, base_min, maximum=False, ledger=ledger)
            total_max = _compose_cost(total_max, base_max, maximum=True, ledger=ledger)
        remaining >>= 1
        if remaining:
            base_min = _compose_cost(base_min, base_min, maximum=False, ledger=ledger)
            base_max = _compose_cost(base_max, base_max, maximum=True, ledger=ledger)
    initial = moore.class_of(edge)
    ends = tuple(j for j in range(n) if total_min[initial][j] is not None)
    minima = [total_min[initial][j] for j in ends]
    maxima = [total_max[initial][j] for j in ends]
    minimum_values = [value for value in minima if value is not None]
    maximum_values = [value for value in maxima if value is not None]
    if len(minimum_values) != len(ends) or len(maximum_values) != len(ends):
        raise AssertionError("closed temporal cylinder lost all continuations")
    next_outputs = tuple(
        sorted(
            {moore.emissions[klass][ingress] for klass in ends for ingress in (0, 1)}
        )
    )
    return TemporalBorderEnvelope(
        moore.observer,
        edge,
        steps,
        moore.initial_class_count,
        moore.state_count,
        moore.rounds,
        next_outputs,
        min(minimum_values),
        max(maximum_values),
        ends,
    )


def _power_temporal_border_with_prefix(
    edge: Edge,
    steps: int,
    observer: TemporalObserver = "gt_high",
    *,
    forced_prefix: tuple[int, int] | None = None,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> TemporalBorderEnvelope:
    """Binary-square a Moore-minimized temporal border relation.

    Exact arithmetic on the finite **overapproximation**: extrema are sound
    bounds for an actual trajectory, and equal extrema authorize an exact
    scalar emission. No future inward carry inputs are guessed or enumerated.
    """
    if (
        type(edge) is not tuple
        or len(edge) != 4
        or any(type(value) is not int or not 0 <= value <= 9 for value in edge)
        or edge not in _EDGE_IDS
    ):
        raise ValueError("temporal border requires a certified cylinder")
    if type(steps) is not int or steps < 0:
        raise ValueError("temporal border duration must be nonnegative")
    if observer not in OBSERVERS or observer == "joint":
        raise ValueError("joint bank is a temporal equality contract, not a scalar sum")
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("temporal border resource owner is incomplete")
    if forced_prefix is not None and (
        type(forced_prefix) is not tuple
        or len(forced_prefix) != 2
        or any(type(bit) is not int or bit not in (0, 1) for bit in forced_prefix)
    ):
        raise ValueError("source carry prefix must contain two exact Boolean ports")
    reservation = (
        nullcontext()
        if ledger is None
        else ledger.reservation(cast(int, scratch_owner), entries=512, nodes=512)
    )
    with reservation:
        moore = minimize_temporal_border(observer, ledger=ledger)
        if forced_prefix is None:
            result = _powered_envelope(moore, edge, steps, ledger=ledger)
        else:
            current = moore.class_of(edge)
            forced_sum = 0
            prefix_length = min(steps, 2)
            for bit in forced_prefix[:prefix_length]:
                forced_sum += moore.emissions[current][bit][0]
                current = moore.transitions[current][bit]
            remaining = steps - prefix_length
            representative_edge = next(
                candidate
                for candidate in EDGE_STATES
                if moore.class_of(candidate) == current
            )
            tail = _powered_envelope(
                moore, representative_edge, remaining, ledger=ledger
            )
            next_outputs = tail.possible_next_outputs
            if steps < 2:
                next_outputs = (moore.emissions[current][forced_prefix[steps]],)
            result = TemporalBorderEnvelope(
                observer,
                edge,
                steps,
                moore.initial_class_count,
                moore.state_count,
                moore.rounds,
                next_outputs,
                forced_sum + tail.minimum_emission_sum,
                forced_sum + tail.maximum_emission_sum,
                tail.possible_end_classes,
            )
    if ledger is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_ENVELOPE_PUBLICATIONS
        )
    return result


def power_temporal_border(
    edge: Edge,
    steps: int,
    observer: TemporalObserver = "gt_high",
    *,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> TemporalBorderEnvelope:
    """Power an unguarded border relation over every inward-carry history.

    Source-derived forced carry ports are intentionally accepted only by the
    family term's internal path after its owner validates an issued prefix.
    """
    return _power_temporal_border_with_prefix(
        edge,
        steps,
        observer,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )


@dataclass(frozen=True, slots=True)
class PumpedTemporalBorderWord:
    """Exact temporal CONCAT/REPEAT emission; no per-generation carry tape."""

    observer: TemporalObserver
    motif: tuple[int, int, int, int]
    repetitions: int
    suffix: tuple[int, ...]

    @property
    def steps(self) -> int:
        return 4 * self.repetitions + len(self.suffix)

    @property
    def emission_sum(self) -> int:
        return self.repetitions * sum(self.motif) + sum(self.suffix)

    def at(self, index: int) -> int:
        if type(index) is not int or not 0 <= index < self.steps:
            raise IndexError(index)
        return self.motif[index % 4]


def pumped_border_word(
    edge: Edge, steps: int, observer: TemporalObserver
) -> PumpedTemporalBorderWord:
    """Universal closed four-phase time word for the forced edge ports.

    On this cylinder growth G is period four with G(p)=[p in (0,3)].
    The two outer decimal-carry pairs have a constant pattern within each
    phase: carry = 2+12*G; reflected XOR = 2-G.  Conditional GT-high and
    raw-borrow ports are deliberately NOT included in this closed formula.
    """
    if edge not in _EDGE_IDS:
        raise ValueError("pumped border requires the certified cylinder")
    if type(steps) is not int or steps < 0:
        raise ValueError("pumped border steps must be nonnegative")
    if observer not in ("growth", "carry_edge", "reflected_xor"):
        raise ValueError("requested border port is conditional, not pumpable")
    a, _, _, z = edge
    phase = (0 if z == 8 else 1) if a == 1 else (3 if z == 8 else 2)
    word = tuple((int((phase + tick) % 4 in (0, 3))) for tick in range(4))
    if observer == "carry_edge":
        motif = tuple(2 + 12 * bit for bit in word)
    elif observer == "reflected_xor":
        motif = tuple(2 - bit for bit in word)
    else:
        motif = word
    repeats, remaining = divmod(steps, 4)
    exact_motif = (motif[0], motif[1], motif[2], motif[3])
    return PumpedTemporalBorderWord(
        observer, exact_motif, repeats, exact_motif[:remaining]
    )


__all__ = [
    "EDGE_STATES",
    "OBSERVERS",
    "PumpedTemporalBorderWord",
    "TemporalBorderEnvelope",
    "TemporalBorderMoore",
    "TemporalObserver",
    "minimize_temporal_border",
    "power_temporal_border",
    "pumped_border_word",
]
