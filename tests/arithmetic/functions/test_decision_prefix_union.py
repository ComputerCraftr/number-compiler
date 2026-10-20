"""Sparse prefix construction preserves exact extensional decision identity."""

from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena


def test_prefix_union_matches_cartesian_builder_with_permuted_order() -> None:
    arena = MultiTerminalDecisionArena((2, 3, 2), order=(1, 2, 0))
    prefixes = ((0, 1), (0,), (2, 0, 1), (1, 0), (1, 1))
    root = arena.build_prefix_union(prefixes)
    assert root == arena.build_prefix_union(reversed(prefixes))
    boxes: list[tuple[bool, tuple[int, ...]]] = []
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


def test_terminal_relabeling_reduces_exact_moore_projection_structurally() -> None:
    arena = MultiTerminalDecisionArena((2, 2))
    root = arena.build(lambda values: (f"endpoint-{values[0]}", f"support-{values[1]}"))
    full = arena.structural_metrics(root)

    def endpoint(value: object) -> object:
        assert isinstance(value, tuple)
        return cast(tuple[object, ...], value)[0]

    projected, projected_root = arena.relabel_terminals(root, endpoint)
    reduced = projected.structural_metrics(projected_root)
    assert full.terminals == 4
    assert full.internal_nodes == 3
    assert reduced.terminals == 2
    assert reduced.internal_nodes == 1
    for left, right in product(range(2), repeat=2):
        assert projected.evaluate(projected_root, (left, right)) == f"endpoint-{left}"


def test_projection_roots_reject_numeric_coercion() -> None:
    arena = MultiTerminalDecisionArena((2,))
    arena.terminal(0)
    with pytest.raises(TypeError, match="exact integer"):
        arena.terminal_value(True)
    with pytest.raises(TypeError, match="exact integer"):
        arena.structural_metrics(False)
    with pytest.raises(TypeError, match="exact integer"):
        arena.relabel_terminals(True, lambda value: value)
