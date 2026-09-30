"""Exact semantic residual quotienting for lazy bimachines.

Powered minimization is based on *functions*, not structural state ids.  The
output relation is resolved once into a reduced multi-terminal decision DAG
(MTDD); exact cofactors of that DAG are the Myhill--Nerode observations used to
minimize the left and right context automata.  This avoids both historical slow
paths:

* no million-entry Python ``(left,symbol,right)->word`` dictionary;
* no dense ``L x A x R`` output grid retained solely for minimization.

The MTDD is a reconvergence-factored exact representation.  Two observations are
merged only when their canonical cofactor roots are identical.  Tropical output-
length shapes are attached as a normalization/pre-signature, but exact cofactor
identity remains mandatory, so tropical algebra can never introduce an unsafe
merge.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.transducer import (
    DFA,
    BimachineTransformResult,
    LazyBimachine,
)
from number_compiler.arithmetic.functions.decision import (
    CanonicalOutputRelation,
    MultiTerminalDecisionArena,
)


class _Interner:
    __slots__ = ("ids",)

    def __init__(self) -> None:
        self.ids: dict[object, int] = {}

    def intern(self, value: object) -> int:
        old = self.ids.get(value)
        if old is not None:
            return old
        q = len(self.ids)
        self.ids[value] = q
        return q


@dataclass(frozen=True, slots=True)
class ResidualMetrics:
    left_before: int
    left_after: int
    right_before: int
    right_after: int
    exact_output_probes: int
    unique_output_words: int
    exact_behavior_vectors: int
    refinement_rounds: int
    decision_description_bytes: int
    alternating_rounds: int = 1
    decision_nodes: int = 0
    decision_groups: int = 0
    decision_selector_bits: int = 0
    canonical_generator_boxes: int = 0
    canonical_regions: int = 0


QuotientBimachine = BimachineTransformResult[ResidualMetrics]


def _refine(
    states: Sequence[int],
    alphabet: Sequence[int],
    step: Callable[[int, int], int | None],
    observation: dict[tuple[int, int], int],
) -> tuple[dict[int, int], int]:
    """Exact deterministic Nerode refinement from canonical output residuals.

    The initial partition is the exact observation row itself rather than one
    undifferentiated class.  Output-equivalent states therefore share their
    canonical id *before* transition refinement starts; later rounds only add
    future-transition information.
    """
    seed = _Interner()
    part = {q: seed.intern(tuple(observation[q, a] for a in alphabet)) for q in states}
    rounds = 0
    while True:
        rounds += 1
        interner = _Interner()
        new: dict[int, int] = {}
        for q in states:
            sig = tuple(
                (
                    part.get(target, -1) if (target := step(q, a)) is not None else -1,
                    observation[q, a],
                )
                for a in alphabet
            )
            new[q] = interner.intern(sig)
        # Partition ids themselves are arbitrary; compare equivalence classes.
        mapped: dict[int, int] = {}
        reverse: dict[int, int] = {}
        stable = True
        for q in states:
            old, nxt = part[q], new[q]
            if old in mapped and mapped[old] != nxt:
                stable = False
                break
            if nxt in reverse and reverse[nxt] != old:
                stable = False
                break
            mapped[old] = nxt
            reverse[nxt] = old
        if stable:
            return new, rounds
        part = new


def quotient_dfa(dfa: DFA, part: dict[int, int]) -> tuple[DFA, dict[int, int]]:
    classes = sorted(set(part.values()))
    rep_old = {c: min(q for q in dfa.states if part[q] == c) for c in classes}
    cmap = {c: i for i, c in enumerate(classes)}
    old_to_new = {q: cmap[part[q]] for q in dfa.states}
    trans = {}
    for c, old in rep_old.items():
        nq = cmap[c]
        for a in dfa.alphabet:
            z = dfa.step(old, a)
            if z is not None:
                trans[nq, a] = old_to_new[z]
    out = DFA(
        dfa.alphabet,
        old_to_new[dfa.start],
        trans,
        tuple(range(len(classes))),
        dfa.right,
    )
    return out, {cmap[c]: rep_old[c] for c in classes}


def _build_output_decision(machine: LazyBimachine) -> CanonicalOutputRelation:
    """Return/install the exact canonical output function.

    Powered composition may already have constructed this relation directly from
    semantic generator boxes.  In that case minimization performs *zero*
    Cartesian output probes.  Only the one-step/reference builder falls back to
    resolving the finite full context domain once.
    """
    existing = machine.canonical_output
    if isinstance(existing, CanonicalOutputRelation):
        return existing
    L, A, R = len(machine.left.states), len(machine.alphabet), len(machine.right.states)
    arena = MultiTerminalDecisionArena((L, A, R), order=(0, 1, 2))
    root = arena.build(
        lambda x: machine.resolver(
            machine.left.states[x[0]],
            machine.alphabet[x[1]],
            machine.right.states[x[2]],
        )
    )
    relation = CanonicalOutputRelation(
        arena, root, machine.left.states, machine.alphabet, machine.right.states
    )
    machine.install_canonical_output(relation)
    return relation


def minimize_bimachine(
    machine: LazyBimachine, *, cache_outputs: bool = False, max_alternations: int = 1
) -> QuotientBimachine:
    """Canonical exact left/right residual quotient.

    The opposite-side automaton need not be alternated after a merge: left-state
    equivalence already requires identical output residuals for every right state
    and symbol, so replacing duplicate left states cannot change equality between
    right residual columns (and symmetrically for right-state merges).  One exact
    MTDD therefore suffices for both partitions.
    """
    before_l, before_r = len(machine.left.states), len(machine.right.states)
    A = machine.alphabet
    output = _build_output_decision(machine)
    decision = output.arena

    # Exact left residuals: functions right_state -> output word.
    lobs: dict[tuple[int, int], int] = {}
    lclasses = _Interner()
    for li, left_state in enumerate(machine.left.states):
        for ai, a in enumerate(A):
            residual = output.cofactor({0: left_state, 1: a})
            shape = decision.tropical_length_shape(residual)
            lobs[left_state, a] = lclasses.intern((shape, residual))
    lpart, lr = _refine(machine.left.states, A, machine.left.step, lobs)

    # Exact right residuals: functions left_state -> output word.
    robs: dict[tuple[int, int], int] = {}
    rclasses = _Interner()
    for ri, r in enumerate(machine.right.states):
        for ai, a in enumerate(A):
            residual = output.cofactor({1: a, 2: r})
            shape = decision.tropical_length_shape(residual)
            robs[r, a] = rclasses.intern((shape, residual))
    rpart, rr = _refine(machine.right.states, A, machine.right.step, robs)

    left, lrep = quotient_dfa(machine.left, lpart)
    right, rrep = quotient_dfa(machine.right, rpart)
    projected = output.project(
        tuple(lrep[q] for q in left.states),
        tuple(rrep[q] for q in right.states),
        new_left=left.states,
        new_right=right.states,
    )
    quotient = LazyBimachine(
        machine.base,
        A,
        left,
        right,
        projected.emit,
        cache_enabled=cache_outputs,
        canonical_output=projected,
    )

    dm = decision.metrics()
    # Terminal count includes the undefined output.  All other terminal values
    # are exact output words.
    unique_words = max(0, dm.terminals - 1)
    from number_compiler.arithmetic.automata.guard import record_residual_metrics

    record_residual_metrics(
        states=len(left.states) + len(right.states),
        output_probes=dm.exact_probes,
        decision_nodes=dm.internal_nodes,
        dependency_groups=dm.dependency_groups,
        selector_bits=dm.selector_bits,
        description_bits=dm.description_bits,
        generator_boxes=dm.generator_boxes,
        canonical_regions=dm.normalized_boxes,
        late_merges=(before_l - len(left.states)) + (before_r - len(right.states)),
    )
    return QuotientBimachine(
        quotient,
        ResidualMetrics(
            before_l,
            len(left.states),
            before_r,
            len(right.states),
            dm.exact_probes,
            unique_words,
            len(lclasses.ids) + len(rclasses.ids),
            lr + rr,
            (dm.description_bits + 7) // 8,
            1,
            dm.internal_nodes,
            dm.dependency_groups,
            dm.selector_bits,
            dm.generator_boxes,
            dm.normalized_boxes,
        ),
    )


__all__ = ["QuotientBimachine", "ResidualMetrics", "minimize_bimachine"]
