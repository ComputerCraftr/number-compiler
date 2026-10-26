"""Ordered interval folds over shared CONCAT/REPEAT grammars."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Protocol, TypeVar

from number_compiler.arithmetic.automata.slp import SLPNode

_FoldValue = TypeVar("_FoldValue")


class SLPNodeArena(Protocol):
    """Read-only node view accepted by shared spatial SLP folds."""

    @property
    def nodes(self) -> Sequence[SLPNode]: ...


def fold_slp_dag(
    arena: SLPNodeArena,
    root: int,
    *,
    empty_value: _FoldValue,
    terminal_value: Callable[[int], _FoldValue],
    concatenate: Callable[[_FoldValue, _FoldValue], _FoldValue],
    repeat: Callable[[_FoldValue, int], _FoldValue],
    on_schedule: Callable[[int], None] | None = None,
    on_pending: Callable[[SLPNode], None] | None = None,
    on_reduce: Callable[[int], None] | None = None,
) -> dict[int, _FoldValue]:
    """Reduce each reachable CONCAT/REPEAT SLP node in child-first order.

    ``on_pending`` observes each unresolved worklist pop; composite nodes are
    observed once before their children and once when their children are ready.
    ``on_reduce`` observes each node exactly once after its value is stored.
    ``on_schedule`` is called before every work item is appended, including the
    initial root task, so callers can reserve worklist capacity incrementally.
    """
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("SLP fold root is invalid")
    values: dict[int, _FoldValue] = {}
    tasks: list[tuple[int, bool]] = []
    value: _FoldValue = empty_value
    try:
        if on_schedule is not None:
            on_schedule(1)
        tasks.append((root, False))
        while tasks:
            node_id, ready = tasks.pop()
            if type(node_id) is not int or not 0 <= node_id < len(arena.nodes):
                raise ValueError("SLP fold child is invalid")
            if node_id in values:
                continue
            node = arena.nodes[node_id]
            if on_pending is not None:
                on_pending(node)
            if not ready:
                if on_schedule is not None:
                    on_schedule(1)
                tasks.append((node_id, True))
                if node.kind == "CONCAT":
                    if on_schedule is not None:
                        on_schedule(1)
                    tasks.append((node.right, False))
                    if on_schedule is not None:
                        on_schedule(1)
                    tasks.append((node.left, False))
                elif node.kind == "REPEAT":
                    if on_schedule is not None:
                        on_schedule(1)
                    tasks.append((node.child, False))
                continue
            if node.kind == "EMPTY":
                value = empty_value
            elif node.kind == "TERM":
                value = terminal_value(node.symbol)
            elif node.kind == "CONCAT":
                value = concatenate(values[node.left], values[node.right])
            elif node.kind == "REPEAT":
                value = repeat(values[node.child], node.count)
            else:
                raise ValueError("unknown SLP node kind")
            values[node_id] = value
            if on_reduce is not None:
                on_reduce(node_id)
        return values
    except BaseException:
        # Callback and reducer failures leave no partial graph pinned by the
        # retained traceback. Caller-owned reservations still unwind normally.
        tasks.clear()
        values.clear()
        value = empty_value
        raise


def fold_slp_interval(
    arena: SLPNodeArena,
    root: int,
    begin: int,
    end: int,
    *,
    identity: _FoldValue,
    length: Callable[[int], int],
    full_value: Callable[[int, bool], _FoldValue],
    compose: Callable[[_FoldValue, _FoldValue], _FoldValue],
    repeat: Callable[[_FoldValue, int], _FoldValue],
    reverse: bool = False,
    on_visit: Callable[[], None] | None = None,
) -> _FoldValue:
    """Fold a symbol interval through shared CONCAT/REPEAT geometry."""
    if not 0 <= root < len(arena.nodes):
        raise ValueError("SLP interval root is invalid")
    if not 0 <= begin <= end <= length(root):
        raise ValueError("SLP interval is outside its encoded word")
    result = identity
    tasks = [(root, begin, end, 1)]
    while tasks:
        node_id, lo, hi, copies = tasks.pop()
        if lo == hi:
            continue
        node_length = length(node_id)
        if on_visit is not None:
            on_visit()
        if not 0 <= lo < hi <= node_length:
            raise ValueError("SLP summary interval escaped its region")
        if lo == 0 and hi == node_length:
            result = compose(result, repeat(full_value(node_id, reverse), copies))
            continue
        node = arena.nodes[node_id]
        pieces: list[tuple[int, int, int, int]] = []
        if node.kind == "CONCAT":
            middle = length(node.left)
            if lo < middle:
                pieces.append((node.left, lo, min(hi, middle), 1))
            if hi > middle:
                pieces.append((node.right, max(lo - middle, 0), hi - middle, 1))
        elif node.kind == "REPEAT":
            child_length = length(node.child)
            if child_length < 1:
                raise ValueError("partial SLP repeat has no symbols")
            first, offset = divmod(lo, child_length)
            last, tail = divmod(hi, child_length)
            if first == last:
                pieces.append((node.child, offset, tail, 1))
            else:
                if offset:
                    pieces.append((node.child, offset, child_length, 1))
                    first += 1
                if last > first:
                    pieces.append((node.child, 0, child_length, last - first))
                if tail:
                    pieces.append((node.child, 0, tail, 1))
        else:
            raise ValueError("partial SLP interval is not a composite")
        tasks.extend(pieces if reverse else reversed(pieces))
    return result
