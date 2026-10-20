from collections.abc import Hashable, Sequence
from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.functions.finite_observer import (
    MAX_FINITE_ORBIT_STATES,
    class_members,
    closed_partition_quotient_rows,
    map_partition_row,
    minimize_finite_observer,
    minimize_finite_orbit,
    partition_equivalent,
    partition_quotient_rows,
    partition_representatives,
    refine_observer_partition,
)
from number_compiler.arithmetic.functions.finite_unary import (
    UnaryTransitionEffect,
    minimize_unary_moore,
    unary_image_filtration,
)


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


def test_partition_helpers_preserve_class_members_and_forbidden_slots() -> None:
    assert class_members((0, 1, 0, 2, 1), 3) == (
        (0, 2),
        (1, 4),
        (3,),
    )
    assert map_partition_row((None, 3, 1), (4, 6, 8, 10)) == (None, 10, 6)
    with pytest.raises(ValueError, match="class count"):
        class_members((0,), -1)
    with pytest.raises(ValueError, match="empty class"):
        class_members((0, 2), 3)
    with pytest.raises(ValueError, match="target leaves"):
        map_partition_row((2,), (0, 1))


def test_partition_quotient_rows_validate_successor_congruence() -> None:
    class_ids = (0, 0, 1, 1)
    assert partition_quotient_rows(
        ((0, None), (1, None), (2, None), (3, None)),
        class_ids,
        2,
    ) == ((0, None), (1, None))
    assert closed_partition_quotient_rows(
        ((0, 1), (1, 0), (2, 3), (3, 2)),
        class_ids,
        2,
    ) == ((0, 0), (1, 1))
    with pytest.raises(ValueError, match="not successor closed"):
        partition_quotient_rows(((0,), (2,), (0,)), (0, 0, 1), 2)
    with pytest.raises(ValueError, match="forbidden edge"):
        closed_partition_quotient_rows(((None,),), (0,), 1)


def test_fixed_point_matches_all_distinguishing_words_on_small_closed_graphs() -> None:
    # A size-three deterministic graph needs at most two strict refinements.
    # This independently compares explicit observation traces, including
    # forbidden ports, against the shared minimizer's resulting classes.
    for targets in product((None, 0, 1, 2), repeat=3):
        rows = tuple((targets[i], (i + 1) % 3) for i in range(3))
        for outputs in product((0, 1), repeat=3):
            signatures: list[tuple[tuple[object, ...], ...]] = []
            for source in range(3):
                traces: list[tuple[object, ...]] = []
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


def test_shared_refinement_and_representatives_keep_ids_observer_local() -> None:
    rows = ((1,), (2,), (2,), (3,))
    labels = ("same", "same", "different", "different")
    previous = (7, 7, 7, 7)
    refined = refine_observer_partition(rows, labels, previous)
    assert partition_equivalent(refined, (0, 0, 1, 1))
    assert partition_representatives(refined, 2) == (0, 2)

    with pytest.raises(ValueError, match="align"):
        refine_observer_partition(rows, labels[:-1], previous)
    with pytest.raises(ValueError, match="exact nonnegative"):
        refine_observer_partition(rows, labels, (0, True, 0, 0))
    with pytest.raises(ValueError, match="declared universe"):
        refine_observer_partition(((4,),), ("x",), (0,))


def test_minimizer_work_callback_reports_each_actual_refinement_pass() -> None:
    visits: list[int] = []
    result = minimize_finite_observer(
        ((1,), (2,), (2,)), (0, 0, 1), on_refinement=visits.append
    )
    assert visits == [3] * result.rounds


def test_closed_orbit_moore_matches_complete_futures_on_small_graphs() -> None:
    for successors in product(range(3), repeat=3):
        for outputs in product((0, 1), repeat=3):
            result = minimize_finite_orbit(successors, outputs)
            traces: list[tuple[int, ...]] = []
            for source in range(3):
                state = source
                trace: list[int] = []
                for _ in range(9):
                    trace.append(outputs[state])
                    state = successors[state]
                traces.append(tuple(trace))
            assert partition_equivalent(result.class_ids, traces)
            for state, class_id in enumerate(result.class_ids):
                assert result.output(class_id) == outputs[state]
                assert result.advance(class_id, 1) == result.class_successors[class_id]


def test_closed_orbit_moore_powers_a_quotient_cycle() -> None:
    result = minimize_finite_orbit((1, 2, 0, 4, 5, 3), (0, 1, 0, 0, 1, 0))
    assert result.class_count == 3
    assert result.class_of(0) == result.class_of(3)
    assert result.advance(result.class_of(0), 10**30 + 2) == result.class_of(0)


def test_closed_orbit_moore_rejects_bad_graphs_before_refinement() -> None:
    with pytest.raises(ValueError, match="at least one"):
        minimize_finite_orbit((), ())
    with pytest.raises(ValueError, match="align"):
        minimize_finite_orbit((0,), ())
    for successor in (True, 1.0, "0", -1, 1):
        with pytest.raises(ValueError, match="successor"):
            minimize_finite_orbit(cast(Sequence[int], (successor,)), ("label",))
    with pytest.raises(ValueError, match="state budget"):
        minimize_finite_orbit((0, 1), ("a", "b"), max_states=1)
    with pytest.raises(ValueError, match="supported bound"):
        minimize_finite_orbit((0,), ("a",), max_states=MAX_FINITE_ORBIT_STATES + 1)
    with pytest.raises(TypeError, match="hashable"):
        minimize_finite_orbit((0,), cast(Sequence[Hashable], (["mutable"],)))
    with pytest.raises(ValueError, match="step count"):
        minimize_finite_orbit((0,), ("a",)).advance(0, True)


@pytest.mark.parametrize("bad", (True, 1.0, "1"))
def test_unary_successors_reject_lossy_integer_aliases(bad: object) -> None:
    with pytest.raises(TypeError, match="unary successor"):
        unary_image_filtration((0, cast(int, bad)))
    with pytest.raises(TypeError, match="unary successor"):
        minimize_unary_moore((0, cast(int, bad)), ("a", "b"))
    with pytest.raises(TypeError, match="unary transition target"):
        UnaryTransitionEffect((0, cast(int, bad)))


def test_closed_orbit_rejects_mutable_hashable_labels() -> None:
    class MutableLabel:
        __hash__ = object.__hash__

    with pytest.raises(TypeError, match="immutable hashable"):
        minimize_finite_orbit((0,), (MutableLabel(),))


def test_closed_orbit_caps_dishonest_sequence_materialization() -> None:
    class Underreported(list[int]):
        def __len__(self) -> int:
            return 1

    with pytest.raises(ValueError, match="sequence length"):
        minimize_finite_orbit(Underreported([0, 0, 0]), ("x",), max_states=1)


def test_closed_orbit_bounds_nested_label_hashing() -> None:
    label: Hashable = "x"
    for _ in range(65):
        label = (label,)
    with pytest.raises(ValueError, match="label structure"):
        minimize_finite_orbit((0,), (label,))
