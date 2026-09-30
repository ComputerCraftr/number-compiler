"""Canonical continuation scheduling for iterative binary and decision queries."""

from __future__ import annotations

from collections.abc import Callable, Container, MutableMapping, Sequence
from typing import TypeVar

T = TypeVar("T")
K = TypeVar("K")
V = TypeVar("V")


def defer_binary_children(
    stack: list[tuple[T, bool]], parent: T, children: Callable[[T], tuple[T, T]]
) -> None:
    """Schedule validated children left-first, then resume their parent."""
    left, right = children(parent)
    stack.extend(((parent, True), (right, False), (left, False)))


def defer_dependencies(
    stack: list[tuple[T, bool]],
    parent: T,
    children: Sequence[T],
    complete: Container[K],
    key: Callable[[T], K],
) -> None:
    stack.append((parent, True))
    for child in reversed(children):
        if key(child) not in complete:
            stack.append((child, False))


def defer_indexed_dependencies(
    stack: list[tuple[T, int, bool]],
    node: T,
    level: int,
    children: Sequence[tuple[T, int]],
    complete: Container[tuple[T, int]],
) -> None:
    stack.append((node, level, True))
    for child_node, child_level in reversed(children):
        if (child_node, child_level) not in complete:
            stack.append((child_node, child_level, False))


def split_choice(
    stack: list[tuple[tuple[int, int, int], bool]],
    splits: MutableMapping[
        tuple[int, int, int], tuple[V, tuple[int, int, int], tuple[int, int, int]]
    ],
    key: tuple[int, int, int],
    variable: V,
    lower: Sequence[int],
    upper: Sequence[int],
) -> None:
    low, high = (lower[0], lower[1], lower[2]), (upper[0], upper[1], upper[2])
    splits[key] = variable, low, high
    stack.extend(((key, True), (high, False), (low, False)))


def push_binary_children(
    stack: list[T], parent: object, left: T | None, right: T | None
) -> None:
    if left is None or right is None:
        raise AssertionError(parent)
    stack.append(right)
    stack.append(left)


def defer_binary_level(
    stack: list[tuple[T, int, bool]],
    node: T,
    level: int,
    low: T,
    high: T,
    complete: Container[tuple[T, int]],
) -> None:
    """Schedule the two next-level restrictions before resuming this decision."""
    defer_indexed_dependencies(
        stack, node, level, ((low, level + 1), (high, level + 1)), complete
    )


def enter_tuple_node(
    stack: list[tuple[object, bool]], active: set[int], value: object
) -> bool:
    """Enter a checked immutable node and schedule tuple members if applicable."""
    active.add(id(value))
    stack.append((value, True))
    if type(value) is tuple:
        stack.extend((item, False) for item in value)
        return True
    return False


def finish_postorder(active: set[int], complete: set[int], identity: int) -> None:
    """Move a completed immutable DAG node out of the active ancestry set."""
    active.remove(identity)
    complete.add(identity)
