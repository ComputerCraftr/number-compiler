"""Shared additive weighted relation identity and composition contracts."""

import pytest

from number_compiler.arithmetic.fields.boolean_transfer import BooleanStateSpace
from number_compiler.arithmetic.fields.weighted_transfer import (
    WeightedTransfer,
    WeightedTransferLaw,
)


def test_weighted_transfer_preserves_all_paths_and_adds_ordered_weights() -> None:
    states = BooleanStateSpace("weighted-test", (0, 1, 2))
    law = WeightedTransferLaw("two-additive-coordinates", ("left", "right"))
    first = WeightedTransfer(
        states,
        law,
        (
            ((1, 2, 3), (2, 1, 0)),
            ((2, 1, 4),),
            (),
        ),
    )
    later = WeightedTransfer(
        states,
        law,
        (
            (),
            ((2, 5, 7),),
            ((2, 3, 2),),
        ),
    )

    composed = first.then(later)
    assert composed.rows == (
        ((2, 4, 2), (2, 7, 10)),
        ((2, 4, 6),),
        (),
    )
    assert WeightedTransfer[int].identity(states, law).then(first) == first


def test_weighted_transfer_rejects_equal_dimension_foreign_owners() -> None:
    states = BooleanStateSpace("weighted-test", (0, 1))
    same_labels_new_owner = BooleanStateSpace("weighted-test", (0, 1))
    law = WeightedTransferLaw("first-law", ("count",))
    other_law = WeightedTransferLaw("first-law", ("count",))
    matrix = WeightedTransfer(states, law, (((1, 1),), ((0, 0),)))
    foreign_space = WeightedTransfer(same_labels_new_owner, law, (((1, 1),), ((0, 0),)))
    foreign_law = WeightedTransfer(states, other_law, (((1, 1),), ((0, 0),)))

    with pytest.raises(ValueError, match="state-space identities"):
        matrix.then(foreign_space)
    with pytest.raises(ValueError, match="law identities"):
        matrix.then(foreign_law)


def test_pointed_deterministic_cycle_skips_repeated_weighted_rows() -> None:
    states = BooleanStateSpace("two-state-cycle", (0, 1))
    law = WeightedTransferLaw("alternating-counts", ("count",))
    matrix = WeightedTransfer(
        states,
        law,
        (((1, 1),), ((0, 2),)),
    )

    result = matrix.power_row_with_work(0, 10**9)
    assert result.row == ((0, 1_500_000_000),)
    assert result.row_evaluations == 2
    assert result.matrix_compositions == 0
    assert result.matrix_squarings == 0
    assert not result.used_branching_fallback


def test_pointed_power_branches_to_exact_general_transfer() -> None:
    states = BooleanStateSpace("branch-then-merge", (0, 1, 2))
    law = WeightedTransferLaw("branch-count", ("count",))
    matrix = WeightedTransfer(
        states,
        law,
        (
            ((0, 1), (1, 3)),
            ((2, 2),),
            ((2, 4),),
        ),
    )

    result = matrix.power_row_with_work(0, 2)
    assert result.row == ((0, 2), (1, 4), (2, 5))
    assert result.row_evaluations == 1
    assert result.matrix_compositions > 0
    assert result.matrix_squarings > 0
    assert result.used_branching_fallback
