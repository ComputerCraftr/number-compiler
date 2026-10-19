"""Shared local reductions for hash-consed temporal output programs."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Protocol, TypeVar


class _RepeatNode(Protocol):
    @property
    def tag(self) -> str: ...

    @property
    def left(self) -> int: ...


_NodeT = TypeVar("_NodeT", bound=_RepeatNode)


def join_equal_repeats(
    left_id: int,
    right_id: int,
    *,
    left_tag: str,
    right_tag: str,
    left_child: int,
    right_child: int,
    left_copies: int,
    right_copies: int,
    repeat: Callable[[int, int], int],
) -> int | None:
    """Coalesce adjacent equal or same-child repeat nodes into one repeat."""
    if left_id == right_id:
        return repeat(left_id, 2)
    if left_tag == "repeat" and right_tag == "repeat" and left_child == right_child:
        return repeat(left_child, left_copies + right_copies)
    return None


def concatenate_temporal_slp(
    left: int,
    right: int,
    *,
    nodes: Sequence[_NodeT],
    repeat: Callable[[int, int], int],
    copies: Callable[[_NodeT], int],
    intern: Callable[[tuple[object, ...], _NodeT], int],
    make_concat: Callable[[int, int, _NodeT, _NodeT], _NodeT],
) -> int:
    """Share empty, repeat-coalescing, and concat publication semantics."""
    if left == 0:
        return right
    if right == 0:
        return left
    left_node, right_node = nodes[left], nodes[right]
    joined = join_equal_repeats(
        left,
        right,
        left_tag=left_node.tag,
        right_tag=right_node.tag,
        left_child=left_node.left,
        right_child=right_node.left,
        left_copies=copies(left_node),
        right_copies=copies(right_node),
        repeat=repeat,
    )
    if joined is not None:
        return joined
    return intern(
        ("concat", left, right),
        make_concat(left, right, left_node, right_node),
    )


__all__ = ["concatenate_temporal_slp", "join_equal_repeats"]
