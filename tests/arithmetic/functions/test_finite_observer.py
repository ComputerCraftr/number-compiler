from itertools import product

import pytest

from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
    partition_equivalent,
)
from number_compiler.arithmetic.functions.finite_unary import minimize_unary_moore


def test_refines_delayed_distinctions_and_preserves_stable_merges() -> None:
    # Sources 0/1 agree through two events but not the third. States 6/7
    # remain indistinguishable on a complete recurrent component.
    rows = ((2,), (3,), (4,), (5,), (6,), (8,), (6,), (7,), (8,))
    labels = (0, 0, 0, 0, 0, 0, 0, 0, 1)
    result = minimize_finite_observer(rows, labels)
    q = result.class_ids
    assert q[0] != q[1]
    assert q[6] == q[7]
    assert result.rounds == 4
    assert result.classes == 5


def test_next_context_is_refined_even_when_next_residual_agrees() -> None:
    # Ordered targets are next context, next residual. Contexts 2 and 3
    # initially look equal; their own successors expose a later difference.
    rows = ((2, 6), (3, 6), (4, 6), (5, 6), (4, 6), (5, 6), (6, 6))
    outputs = ("residual", "residual", "context", "context", "LT", "GT", "sink")
    result = minimize_finite_observer(rows, outputs)
    assert result.class_ids[0] != result.class_ids[1]
    assert result.rounds == 3


def test_admission_is_observable_and_frontier_references_are_rejected() -> None:
    assert minimize_finite_observer(((None,), (1,)), (0, 0)).classes == 2
    for rows in (((2,), (1,)), ((-1,), (1,)), ((True,), (1,)), ((0,), ())):
        with pytest.raises(ValueError):
            minimize_finite_observer(rows, (0, 0))


def test_fixed_point_matches_all_distinguishing_words_on_small_closed_graphs() -> None:
    # A size-three deterministic graph needs at most two strict refinements.
    # This independently compares explicit observation traces, including
    # forbidden ports, against the shared minimizer's resulting classes.
    for targets in product((None, 0, 1, 2), repeat=3):
        rows = tuple((targets[i], (i + 1) % 3) for i in range(3))
        for outputs in product((0, 1), repeat=3):
            signatures = []
            for source in range(3):
                traces = []
                for word in product((0, 1), repeat=3):
                    state = source
                    trace: list[object] = [outputs[state]]
                    for letter in word:
                        target = rows[state][letter]
                        if target is None:
                            trace.append(None)
                            break
                        state = target
                        trace.append(outputs[state])
                    traces.append(tuple(trace))
                signatures.append(tuple(traces))
            result = minimize_finite_observer(rows, outputs)
            assert partition_equivalent(result.class_ids, signatures)
            # The returned graph is actually stable on every admitted edge.
            for x, y in product(range(3), repeat=2):
                if result.class_ids[x] == result.class_ids[y]:
                    assert outputs[x] == outputs[y]
                    for a, b in zip(rows[x], rows[y], strict=True):
                        assert (a is None) == (b is None)
                        if a is not None and b is not None:
                            assert result.class_ids[a] == result.class_ids[b]


def test_unary_uses_the_same_owner_and_keeps_its_public_result() -> None:
    result = minimize_unary_moore((1, 2, 2), (0, 0, 1))
    generic = minimize_finite_observer(((1,), (2,), (2,)), (0, 0, 1))
    assert (result.classes, result.class_ids, result.rounds) == (
        generic.classes,
        generic.class_ids,
        generic.rounds,
    )
