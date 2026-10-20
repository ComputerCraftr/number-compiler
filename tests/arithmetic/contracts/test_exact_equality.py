from number_compiler.arithmetic.contracts.exact_equality import (
    extend_typed_tuple_pairs,
    typed_tuple_tree_equal,
)


def test_typed_tuple_tree_equality_is_iterative_and_type_sensitive() -> None:
    left: object = (0,)
    right: object = (0,)
    for _ in range(1500):
        left = (left,)
        right = (right,)

    assert typed_tuple_tree_equal(left, right)
    assert not typed_tuple_tree_equal((True,), (1,))
    assert not typed_tuple_tree_equal((1,), (1, 2))


def test_tuple_pair_expansion_checks_length_before_appending() -> None:
    pending: list[tuple[object, object]] = []

    assert extend_typed_tuple_pairs(pending, (1, True), (2, False))
    assert pending == [(1, 2), (True, False)]
    assert not extend_typed_tuple_pairs(pending, (1,), ())
    assert pending == [(1, 2), (True, False)]
