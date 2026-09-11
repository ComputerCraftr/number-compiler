"""Sparse prefix construction preserves exact extensional decision identity."""

from itertools import product

import pytest

from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena


def test_prefix_union_matches_cartesian_builder_with_permuted_order() -> None:
    arena = MultiTerminalDecisionArena((2, 3, 2), order=(1, 2, 0))
    prefixes = ((0, 1), (0,), (2, 0, 1), (1, 0), (1, 1))
    root = arena.build_prefix_union(prefixes)
    assert root == arena.build_prefix_union(reversed(prefixes))
    boxes = []
    for prefix in prefixes:
        masks = [3, 7, 3]
        for level, value in enumerate(prefix):
            masks[arena.order[level]] = 1 << value
        boxes.append((True, tuple(masks)))
    assert root == arena.build_labeled_boxes(boxes, default=False)
    for values in product(range(2), range(3), range(2)):
        ordered = tuple(values[i] for i in arena.order)
        expected = any(ordered[: len(p)] == p for p in prefixes)
        assert arena.evaluate(root, values) == expected
    assert arena.build_prefix_union(()) == arena.terminal(False)
    assert arena.build_prefix_union(((),)) == arena.terminal(True)


def test_prefix_validation_is_not_hidden_by_subsumption() -> None:
    arena = MultiTerminalDecisionArena((2, 2))
    for invalid in ((2,), (True,), (0, 0, 0)):
        with pytest.raises(ValueError, match="prefix"):
            arena.build_prefix_union(((), invalid))
