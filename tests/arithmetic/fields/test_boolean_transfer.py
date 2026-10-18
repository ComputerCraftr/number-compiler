"""Independent finite-relation checks for shared conditional matrix powering."""

import pytest

from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanMatrix,
    BooleanStateSpace,
    boolean_rows_image,
    boolean_rows_power,
    boolean_rows_then,
)


def test_boolean_transfer_chronology_and_conditional_union() -> None:
    first = (0b110, 0b001, 0)
    after = (0b100, 0b010, 0b001)
    expected = tuple(
        sum(
            1 << target
            for target in range(3)
            if any(
                first[source] & (1 << middle) and after[middle] & (1 << target)
                for middle in range(3)
            )
        )
        for source in range(3)
    )
    assert boolean_rows_then(first, after) == expected
    assert boolean_rows_then(first, after) != boolean_rows_then(after, first)
    assert boolean_rows_image(first, 0b011) == 0b111


@pytest.mark.parametrize("rows", [(), (0,), (1,), (2, 4, 3), (3, 6, 12, 9)])
def test_boolean_transfer_binary_powers_match_path_sets(rows: tuple[int, ...]) -> None:
    paths = [{source} for source in range(len(rows))]
    for count in range(17):
        assert boolean_rows_power(rows, count) == tuple(
            sum(1 << target for target in targets) for targets in paths
        )
        paths = [
            {
                target
                for middle in targets
                for target in range(len(rows))
                if rows[middle] & (1 << target)
            }
            for targets in paths
        ]


def test_boolean_transfer_rejects_outside_states_and_boolean_counts() -> None:
    for rows in ((-1,), (2,), (True,)):
        with pytest.raises(ValueError):
            boolean_rows_power(rows, 1)
    with pytest.raises(ValueError):
        boolean_rows_then((1,), (1, 2))
    for count in (-1, True):
        with pytest.raises(ValueError):
            boolean_rows_power((1,), count)
    for sources in (-1, 2, True):
        with pytest.raises(ValueError):
            boolean_rows_image((1,), sources)


def test_typed_boolean_matrices_require_the_same_state_space_owner() -> None:
    first_space = BooleanStateSpace("decimal-pair", ((0, 0), (0, 1)))
    same_shape_space = BooleanStateSpace("decimal-pair", ((0, 0), (0, 1)))
    first = BooleanMatrix(first_space, (0b10, 0b01))
    after = BooleanMatrix(first_space, (0b01, 0b10))
    foreign = BooleanMatrix(same_shape_space, (0b01, 0b10))

    assert first_space is not same_shape_space
    assert first_space != same_shape_space
    assert first.then(after).rows == (0b10, 0b01)
    assert first.power(0) == BooleanMatrix.identity(first_space)
    assert first.image(0b01) == 0b10
    with pytest.raises(ValueError, match="state-space identities"):
        first.then(foreign)


def test_typed_boolean_matrix_rejects_malformed_state_owners_and_rows() -> None:
    with pytest.raises(ValueError, match="unique ordered states"):
        BooleanStateSpace("duplicate", (0, 0))
    space = BooleanStateSpace("two-state", (0, 1))
    with pytest.raises(ValueError, match="do not match"):
        BooleanMatrix(space, (0b01,))
    with pytest.raises(ValueError, match="do not match"):
        BooleanMatrix(space, (0b100, 0))
