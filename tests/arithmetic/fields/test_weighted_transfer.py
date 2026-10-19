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
    assert WeightedTransfer.identity(states, law).then(first) == first


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
