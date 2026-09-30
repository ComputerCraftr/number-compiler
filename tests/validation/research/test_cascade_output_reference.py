from __future__ import annotations

from collections.abc import Callable
from typing import Never

import pytest

from devtools.experiments.reverse_add.cascade_output_reference import (
    ReferenceCascadeComposition,
    compose_reference_cascade,
    normalize_unary_cascade_output,
    normalize_unary_cascade_output_measured,
)
from number_compiler.arithmetic.automata.transducer import DFA, LazyBimachine
from number_compiler.arithmetic.functions.decision import (
    CanonicalOutputRelation,
    MultiTerminalDecisionArena,
)


def _machine(
    emit: Callable[[int, int, int], tuple[int, ...] | None],
) -> LazyBimachine:
    alphabet = (0, 1)
    transitions = {
        (state, symbol): state ^ symbol for state in range(2) for symbol in alphabet
    }
    left = DFA(alphabet, 0, transitions, (0, 1), False)
    right = DFA(alphabet, 0, transitions, (0, 1), True)
    arena = MultiTerminalDecisionArena((2, 2, 2))
    root = arena.build(lambda row: emit(row[0], row[1], row[2]))
    relation = CanonicalOutputRelation(arena, root, (0, 1), alphabet, (0, 1))
    return LazyBimachine(
        2,
        alphabet,
        left,
        right,
        relation.emit,
        cache_enabled=False,
        canonical_output=relation,
    )


def _composed_fixture() -> tuple[
    LazyBimachine, LazyBimachine, ReferenceCascadeComposition
]:
    first = _machine(lambda left, symbol, right: (left ^ symbol ^ right,))
    second = _machine(lambda left, symbol, right: (symbol ^ (left & right),))
    return first, second, compose_reference_cascade(first, second, cache_outputs=False)


def test_unary_cascade_normalizer_eliminates_witness_resolver() -> None:
    first, second, composition = _composed_fixture()
    assert composition.complete and composition.machine is not None
    machine = composition.machine
    expected = {
        (left, symbol, right): machine.emit(left, symbol, right)
        for left in machine.left.states
        for symbol in machine.alphabet
        for right in machine.right.states
    }

    def forbidden(_left: int, _symbol: int, _right: int) -> Never:
        raise AssertionError("canonical normalization called the witness resolver")

    machine.resolver = forbidden
    relation = normalize_unary_cascade_output(first, second, composition)
    assert machine.canonical_output is relation
    assert machine.cached_outputs == 0
    assert {key: relation.emit(*key) for key in expected} == expected


def test_normalizer_binds_exact_cascade_constructors_and_reports_work() -> None:
    first, second, composition = _composed_fixture()
    foreign = _machine(lambda left, symbol, right: (left ^ symbol ^ right,))
    with pytest.raises(ValueError, match="foreign constructors"):
        normalize_unary_cascade_output(foreign, second, composition)
    assert composition.machine is not None
    assert composition.machine.canonical_output is None

    result = normalize_unary_cascade_output_measured(
        first, second, composition, order=(1, 0, 2)
    )
    assert result.relation is composition.machine.canonical_output
    assert result.work.producer_boxes > 0
    assert result.work.consumer_box_pairs > 0
    assert result.work.producer_transition_edges > 0
    assert result.work.transition_group_pairs > 0
    assert result.work.relation_box_probes > 0
    assert result.work.axis_box_probes > 0
    assert result.work.axis_selector_cache_hits > 0
    assert result.work.selected_box_projections > 0
    assert result.work.generated_boxes > 0
    assert result.work.normalized_boxes > 0
    assert result.work.decision_nodes > 0
    assert result.work.variable_order == (1, 0, 2)


def test_normalizer_rejects_mutated_inputs_and_external_publication() -> None:
    first, second, composition = _composed_fixture()
    assert composition.machine is not None
    transition = next(iter(first.left.trans))
    old_target = first.left.trans[transition]
    first.left.trans[transition] = old_target ^ 1
    with pytest.raises(ValueError, match="changed after construction"):
        normalize_unary_cascade_output(first, second, composition)
    assert composition.machine.canonical_output is None
    first.left.trans[transition] = old_target

    composition.machine.canonical_output = first.canonical_output
    with pytest.raises(ValueError, match="published outside normalization"):
        normalize_unary_cascade_output(first, second, composition)

    replacement = compose_reference_cascade(first, second, cache_outputs=False)
    assert replacement.machine is not None
    original_left = replacement.machine.left
    altered = dict(original_left.trans)
    transition = next(iter(altered))
    altered[transition] ^= 1
    replacement.machine.left = DFA(
        original_left.alphabet,
        original_left.start,
        altered,
        original_left.states,
        original_left.right,
    )
    with pytest.raises(ValueError, match="machine contexts changed"):
        normalize_unary_cascade_output(first, second, replacement)


@pytest.mark.parametrize(
    "word",
    ((0,), (1,), (0, 1), (1, 1, 0), (0, 1, 0, 1, 1)),
)
def test_normalized_cascade_matches_chronological_word_composition(
    word: tuple[int, ...],
) -> None:
    first, second, composition = _composed_fixture()
    normalize_unary_cascade_output(first, second, composition)
    assert composition.machine is not None
    assert composition.machine.output(word) == second.output(first.output(word))


def test_normalizer_rejects_nonunary_producer_without_deferred_evaluation() -> None:
    first = _machine(lambda _left, symbol, _right: (symbol, symbol))
    second = _machine(lambda left, symbol, right: (left ^ symbol ^ right,))
    composition = compose_reference_cascade(first, second, cache_outputs=False)
    assert composition.complete and composition.machine is not None

    def forbidden(_left: int, _symbol: int, _right: int) -> Never:
        raise AssertionError("unary admission called the witness resolver")

    composition.machine.resolver = forbidden
    with pytest.raises(ValueError, match="one producer symbol"):
        normalize_unary_cascade_output(first, second, composition)
    assert composition.machine.canonical_output is None
