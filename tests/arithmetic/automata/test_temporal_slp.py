"""Shared temporal SLP concatenation preserves empty and repeat reductions."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.temporal_slp import (
    concatenate_temporal_slp,
)


@dataclass(frozen=True, slots=True)
class _Node:
    tag: str
    left: int
    right: int = 0
    copies: int = 1


def test_empty_children_and_equal_repeat_nodes_are_coalesced() -> None:
    nodes = [_Node("empty", 0), _Node("leaf", 0)]

    def repeat(child: int, copies: int) -> int:
        nodes.append(_Node("repeat", child, copies=copies))
        return len(nodes) - 1

    def intern(_key: tuple[object, ...], node: _Node) -> int:
        nodes.append(node)
        return len(nodes) - 1

    def make_concat(left: int, right: int, _left: _Node, _right: _Node) -> _Node:
        return _Node("concat", left, right)

    assert (
        concatenate_temporal_slp(
            0,
            1,
            nodes=nodes,
            repeat=repeat,
            copies=lambda node: node.copies,
            intern=intern,
            make_concat=make_concat,
        )
        == 1
    )
    assert (
        concatenate_temporal_slp(
            1,
            1,
            nodes=nodes,
            repeat=repeat,
            copies=lambda node: node.copies,
            intern=intern,
            make_concat=make_concat,
        )
        == 2
    )
    assert nodes[2] == _Node("repeat", 1, copies=2)


def test_adjacent_same_child_repeats_merge_without_expanding() -> None:
    nodes = [
        _Node("empty", 0),
        _Node("leaf", 0),
        _Node("repeat", 1, copies=3),
        _Node("repeat", 1, copies=5),
    ]

    def repeat(child: int, copies: int) -> int:
        nodes.append(_Node("repeat", child, copies=copies))
        return len(nodes) - 1

    result = concatenate_temporal_slp(
        2,
        3,
        nodes=nodes,
        repeat=repeat,
        copies=lambda node: node.copies,
        intern=lambda _key, _node: -1,
        make_concat=lambda left, right, _left, _right: _Node("concat", left, right),
    )
    assert result == 4
    assert nodes[result] == _Node("repeat", 1, copies=8)


def test_distinct_children_publish_one_concat() -> None:
    nodes = [_Node("empty", 0), _Node("leaf", 0), _Node("leaf", 0)]

    def repeat(child: int, copies: int) -> int:
        nodes.append(_Node("repeat", child, copies=copies))
        return len(nodes) - 1

    def intern(_key: tuple[object, ...], node: _Node) -> int:
        nodes.append(node)
        return len(nodes) - 1

    result = concatenate_temporal_slp(
        1,
        2,
        nodes=nodes,
        repeat=repeat,
        copies=lambda node: node.copies,
        intern=intern,
        make_concat=lambda left, right, _left, _right: _Node("concat", left, right),
    )
    assert result == 3
    assert nodes[result] == _Node("concat", 1, 2)
