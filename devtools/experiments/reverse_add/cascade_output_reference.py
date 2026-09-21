"""Finite unary cascade-output reference experiment.

This is diagnostic finite-algebra code, not an installed reverse/add constructor
and not a source-bound complete range return. It remains under ``devtools``
because it constructs universal contexts before quotienting, which is the wrong
production state space regardless of timing. It also lacks complete thirteen-
channel source authority; its D4 resource failure is diagnostic evidence only.

Within that scope, the grouped cascade compiler closes two context automata
without retaining Cartesian witness triples. This reference performs the
remaining relational join for length-preserving unary producers and builds an
authoritative MTDD without calling the witness-search resolver.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from devtools.experiments.reverse_add.cascade_power import (
    CascadeComposition,
    CascadeContextDFA,
    compose_bimachines_cascade,
)
from number_compiler.arithmetic.automata.transducer import DFA, LazyBimachine
from number_compiler.arithmetic.functions.decision import (
    CanonicalOutputRelation,
    MultiTerminalDecisionArena,
)

_Box = tuple[int, int, int]


def _dfa_snapshot(dfa: DFA) -> tuple[object, ...]:
    return (
        dfa.alphabet,
        dfa.start,
        tuple(sorted(dfa.trans.items())),
        dfa.states,
        dfa.right,
    )


def _machine_snapshot(machine: LazyBimachine) -> tuple[object, ...]:
    output = machine.canonical_output
    return (
        machine.base,
        machine.alphabet,
        _dfa_snapshot(machine.left),
        _dfa_snapshot(machine.right),
        None if output is None else tuple(output.iter_boxes(include_undefined=True)),
    )


def _context_snapshot(context: CascadeContextDFA) -> tuple[object, ...]:
    return (
        context.alphabet,
        context.start,
        tuple(sorted(context.trans.items())),
        context.states,
        context.right,
        context.complete,
        tuple((state, tuple(context.boxes(state))) for state in context.states),
    )


@dataclass(frozen=True, slots=True)
class ReferenceCascadeComposition:
    """Identity and semantic snapshots for one finite reference cascade."""

    composition: CascadeComposition
    first: LazyBimachine
    second: LazyBimachine
    first_snapshot: tuple[object, ...]
    second_snapshot: tuple[object, ...]
    left_snapshot: tuple[object, ...]
    right_snapshot: tuple[object, ...]

    @property
    def machine(self) -> LazyBimachine | None:
        return self.composition.machine

    @property
    def left(self) -> CascadeContextDFA:
        return self.composition.left

    @property
    def right(self) -> CascadeContextDFA:
        return self.composition.right

    @property
    def complete(self) -> bool:
        return self.composition.complete


def bind_reference_cascade(
    first: LazyBimachine,
    second: LazyBimachine,
    composition: CascadeComposition,
) -> ReferenceCascadeComposition:
    """Seal the mutable finite objects used by one reference normalization."""
    return ReferenceCascadeComposition(
        composition,
        first,
        second,
        _machine_snapshot(first),
        _machine_snapshot(second),
        _context_snapshot(composition.left),
        _context_snapshot(composition.right),
    )


def compose_reference_cascade(
    first: LazyBimachine,
    second: LazyBimachine,
    *,
    left_order: Sequence[int] = (0, 1, 2),
    right_order: Sequence[int] = (2, 1, 0),
    state_cap: int | None = None,
    time_cap: float | None = None,
    cache_outputs: bool = False,
) -> ReferenceCascadeComposition:
    """Construct and immediately seal a finite research cascade."""
    return bind_reference_cascade(
        first,
        second,
        compose_bimachines_cascade(
            first,
            second,
            left_order=left_order,
            right_order=right_order,
            state_cap=state_cap,
            time_cap=time_cap,
            cache_outputs=cache_outputs,
        ),
    )


def _values(mask: int) -> Iterable[int]:
    value = int(mask)
    while value:
        bit = value & -value
        yield bit.bit_length() - 1
        value ^= bit


def _transition_groups(dfa: DFA, symbol: int, source_mask: int) -> dict[int, int]:
    """Group a selected deterministic transition graph by target state."""
    groups: dict[int, int] = {}
    for source in _values(source_mask):
        target = dfa.step(source, symbol)
        if target is not None:
            groups[target] = groups.get(target, 0) | (1 << source)
    return groups


class _RelationBoxIndex:
    """Memoized existential box queries over canonical cascade relations."""

    __slots__ = ("_axis", "_boxes", "_memo", "_work")

    def __init__(
        self, contexts: CascadeContextDFA, work: CascadeOutputNormalizationWork
    ) -> None:
        boxes: list[tuple[int, _Box]] = []
        for state in contexts.states:
            state_bit = 1 << state
            boxes.extend((state_bit, (x, y, z)) for x, y, z in contexts.boxes(state))
        self._boxes = tuple(boxes)
        self._memo: dict[_Box, int] = {}
        self._axis: dict[tuple[int, int], int] = {}
        self._work = work

    def _axis_intersections(self, axis: int, selector: int) -> int:
        key = axis, selector
        old = self._axis.get(key)
        if old is not None:
            self._work.axis_selector_cache_hits += 1
            return old
        selected = 0
        for index, (_state, box) in enumerate(self._boxes):
            self._work.axis_box_probes += 1
            if box[axis] & selector:
                selected |= 1 << index
        self._axis[key] = selected
        return selected

    def intersecting_states(self, constraint: _Box) -> int:
        old = self._memo.get(constraint)
        if old is not None:
            self._work.relation_box_cache_hits += 1
            return old
        selected = 0
        a, b, c = constraint
        box_bits = (
            self._axis_intersections(0, a)
            & self._axis_intersections(1, b)
            & self._axis_intersections(2, c)
        )
        while box_bits:
            bit = box_bits & -box_bits
            box_bits ^= bit
            self._work.selected_box_projections += 1
            selected |= self._boxes[bit.bit_length() - 1][0]
        self._work.relation_box_probes = (
            self._work.axis_box_probes + self._work.selected_box_projections
        )
        self._memo[constraint] = selected
        return selected


def _checked_relation(machine: LazyBimachine, role: str) -> CanonicalOutputRelation:
    relation = machine.canonical_output
    if relation is None:
        raise ValueError(f"{role} requires an authoritative canonical output relation")
    if (
        relation.left_states != machine.left.states
        or relation.alphabet != machine.alphabet
        or relation.right_states != machine.right.states
    ):
        raise ValueError(f"{role} canonical output has another machine domain")
    return relation


@dataclass(slots=True)
class CascadeOutputNormalizationWork:
    """Actual relational work performed by one canonical normalization."""

    producer_boxes: int = 0
    consumer_box_pairs: int = 0
    producer_transition_edges: int = 0
    transition_group_pairs: int = 0
    relation_box_probes: int = 0
    relation_box_cache_hits: int = 0
    axis_box_probes: int = 0
    axis_selector_cache_hits: int = 0
    selected_box_projections: int = 0
    generated_boxes: int = 0
    normalized_boxes: int = 0
    decision_nodes: int = 0
    variable_order: tuple[int, int, int] = (0, 1, 2)


@dataclass(frozen=True, slots=True)
class CascadeOutputNormalization:
    relation: CanonicalOutputRelation
    work: CascadeOutputNormalizationWork


def normalize_unary_cascade_output_measured(
    first: LazyBimachine,
    second: LazyBimachine,
    composition: ReferenceCascadeComposition,
    *,
    order: tuple[int, int, int] = (0, 1, 2),
) -> CascadeOutputNormalization:
    """Eliminate internal contexts and install ``second(first(symbol))``.

    ``first`` must be length preserving at each local emission.  This is the
    fixed-padded reverse/add contract: growth occupies an admitted blank cell,
    rather than changing a fragment's length.  Output words of ``second`` remain
    exact terminal labels, although the same padded contract normally makes
    them unary too.

    Work is over canonical output regions, deterministic transition groups and
    dependency-relation boxes.  It never evaluates a composed left/right
    context pair and never calls the cascade's deferred resolver.
    """
    if first.alphabet != second.alphabet:
        raise ValueError("cascade output normalization requires one alphabet")
    if type(order) is not tuple or sorted(order) != [0, 1, 2]:
        raise ValueError("cascade output normalization requires a variable permutation")
    if composition.first is not first or composition.second is not second:
        raise ValueError("cascade output normalization has foreign constructors")
    if (
        composition.first_snapshot != _machine_snapshot(first)
        or composition.second_snapshot != _machine_snapshot(second)
        or composition.left_snapshot != _context_snapshot(composition.left)
        or composition.right_snapshot != _context_snapshot(composition.right)
    ):
        raise ValueError("cascade output inputs changed after construction")
    for dfa in (first.left, first.right, second.left, second.right):
        if dfa.states != tuple(range(len(dfa.states))):
            raise ValueError("cascade output normalization requires dense state ids")
    if not composition.complete or composition.machine is None:
        raise ValueError("cascade output normalization requires closed contexts")
    machine = composition.machine
    if (
        first.base != second.base
        or machine.base != first.base
        or machine.alphabet != first.alphabet
        or machine.left.states != composition.left.states
        or machine.right.states != composition.right.states
    ):
        raise ValueError("cascade output machine has another context domain")
    if (
        _dfa_snapshot(machine.left) != composition.left_snapshot[:5]
        or _dfa_snapshot(machine.right) != composition.right_snapshot[:5]
    ):
        raise ValueError("cascade output machine contexts changed after construction")
    first_output = _checked_relation(first, "cascade producer")
    second_output = _checked_relation(second, "cascade consumer")
    if machine.canonical_output is not None:
        raise ValueError("cascade output relation was published outside normalization")

    work = CascadeOutputNormalizationWork(variable_order=order)
    left_index = _RelationBoxIndex(composition.left, work)
    right_index = _RelationBoxIndex(composition.right, work)
    generators: list[tuple[tuple[int, ...], tuple[int, int, int]]] = []

    for symbol_index, symbol in enumerate(first.alphabet):
        symbol_mask = 1 << symbol_index
        for middle, (
            producer_left,
            _producer_symbol,
            producer_right,
        ) in first_output.iter_boxes(symbol=symbol):
            work.producer_boxes += 1
            if middle is None:
                continue
            if len(middle) != 1:
                raise ValueError(
                    "unary cascade output normalization requires one producer symbol"
                )
            middle_symbol = middle[0]
            if middle_symbol not in second.alphabet:
                raise ValueError(
                    "cascade producer emitted outside the consumer alphabet"
                )
            left_edges = _transition_groups(first.left, symbol, int(producer_left))
            right_edges = _transition_groups(first.right, symbol, int(producer_right))
            work.producer_transition_edges += int(producer_left).bit_count()
            work.producer_transition_edges += int(producer_right).bit_count()
            for output, (
                consumer_left,
                _middle_mask,
                consumer_right,
            ) in second_output.iter_boxes(symbol=middle_symbol):
                if output is None:
                    continue
                work.consumer_box_pairs += 1
                for left_after, left_before in left_edges.items():
                    for right_before, right_after in right_edges.items():
                        work.transition_group_pairs += 1
                        # Left dependency coordinates are
                        # (first-left-before, second-left-before,
                        #  first-right-before).  Right coordinates are
                        # (first-left-after, second-right-after,
                        #  first-right-after).
                        selected_left = left_index.intersecting_states(
                            (left_before, int(consumer_left), 1 << right_before)
                        )
                        if not selected_left:
                            continue
                        selected_right = right_index.intersecting_states(
                            (1 << left_after, int(consumer_right), right_after)
                        )
                        if selected_right:
                            work.generated_boxes += 1
                            generators.append(
                                (
                                    tuple(output),
                                    (selected_left, symbol_mask, selected_right),
                                )
                            )

    arena = MultiTerminalDecisionArena(
        (len(machine.left.states), len(machine.alphabet), len(machine.right.states)),
        order=order,
    )
    try:
        root = arena.build_labeled_boxes(generators, default=None)
    except AssertionError as error:
        if "overlapping canonical output boxes disagree" not in str(error):
            raise
        raise ValueError(
            "cascade output witnesses disagree after elimination"
        ) from error
    relation = CanonicalOutputRelation(
        arena,
        root,
        machine.left.states,
        machine.alphabet,
        machine.right.states,
    )
    decision_metrics = arena.metrics()
    work.normalized_boxes = decision_metrics.normalized_boxes
    work.decision_nodes = decision_metrics.internal_nodes
    machine.install_canonical_output(relation)
    return CascadeOutputNormalization(relation, work)


def normalize_unary_cascade_output(
    first: LazyBimachine,
    second: LazyBimachine,
    composition: ReferenceCascadeComposition,
    *,
    order: tuple[int, int, int] = (0, 1, 2),
) -> CanonicalOutputRelation:
    """Install and return the canonical relation, omitting measured metadata."""
    return normalize_unary_cascade_output_measured(
        first, second, composition, order=order
    ).relation


__all__ = [
    "CascadeOutputNormalization",
    "CascadeOutputNormalizationWork",
    "ReferenceCascadeComposition",
    "bind_reference_cascade",
    "compose_reference_cascade",
    "normalize_unary_cascade_output",
    "normalize_unary_cascade_output_measured",
]
