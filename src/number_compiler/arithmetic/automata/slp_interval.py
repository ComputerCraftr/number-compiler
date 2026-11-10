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
    on_evaluate: Callable[[int], None] | None = None,
    on_unschedule: Callable[[int], None] | None = None,
    reclaim_values: bool = False,
    on_reference_entry: Callable[[int], None] | None = None,
    on_reference_release: Callable[[int], None] | None = None,
    on_value_release: Callable[[int], None] | None = None,
) -> dict[int, _FoldValue]:
    """Reduce each reachable CONCAT/REPEAT SLP node in child-first order.

    ``on_pending`` observes each unresolved worklist pop; composite nodes are
    observed once before their children and once when their children are ready.
    ``on_reduce`` observes each node exactly once after its value is stored.
    ``on_schedule`` is called before every work item is appended, including the
    initial root task, so callers can reserve worklist capacity incrementally.
    ``on_evaluate`` precedes each result construction and dictionary insertion,
    so a consumer can reserve its actual summary payload before allocation.
    ``on_unschedule`` follows each worklist pop, including memo skips, and
    releases any live-task charge. If evaluation fails, queued tasks are
    cleared and their charge released before the exception is re-raised.
    With ``reclaim_values``, a charged depth-first, color-marked prewalk rejects
    cycles and counts each incoming child edge without assuming node IDs are
    topologically ordered. It preserves each shared child value until its
    final parent has consumed it, then releases that value exactly once. Only
    the root value remains in the returned map.
    Callbacks charge/release reference rows and values before/after their
    respective lifetime; the caller's reservation owns cleanup on failure.
    """
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("SLP fold root is invalid")
    if type(reclaim_values) is not bool:
        raise TypeError("SLP value-reclamation selector must be Boolean")
    if not reclaim_values and any(
        callback is not None
        for callback in (on_reference_entry, on_reference_release, on_value_release)
    ):
        raise ValueError("SLP reclamation callbacks require value reclamation")
    values: dict[int, _FoldValue] = {}
    tasks: list[tuple[int, bool]] = []
    # Encode incoming-reference count and prewalk color in one integer:
    # 3 * count + {0: scheduled, 1: active, 2: complete}.
    remaining_uses: dict[int, int] = {}
    value: _FoldValue = empty_value
    children: tuple[int, ...] = ()

    def pop_task() -> tuple[int, bool]:
        item = tasks.pop()
        if on_unschedule is not None:
            on_unschedule(1)
        if type(item[0]) is not int or not 0 <= item[0] < len(arena.nodes):
            raise ValueError("SLP fold child is invalid")
        return item

    try:
        if reclaim_values:
            if on_reference_entry is not None:
                on_reference_entry(root)
            remaining_uses[root] = 0
            if on_schedule is not None:
                on_schedule(1)
            tasks.append((root, False))
            while tasks:
                node_id, exiting = pop_task()
                reference_state = remaining_uses[node_id]
                color = reference_state % 3
                uses = reference_state // 3
                if exiting:
                    if color != 1:
                        raise ValueError(
                            "SLP fold grammar has an invalid traversal state"
                        )
                    remaining_uses[node_id] = uses * 3 + 2
                    continue
                if color == 2:
                    continue
                if color != 0:
                    raise ValueError("SLP fold grammar contains a cycle")
                remaining_uses[node_id] = uses * 3 + 1
                node = arena.nodes[node_id]
                if node.kind == "CONCAT":
                    children = (node.left, node.right)
                elif node.kind == "REPEAT":
                    children = (node.child,)
                elif node.kind in ("EMPTY", "TERM"):
                    children = ()
                else:
                    raise ValueError("unknown SLP node kind")
                if on_schedule is not None:
                    on_schedule(1)
                tasks.append((node_id, True))
                for child in reversed(children):
                    if type(child) is not int or not 0 <= child < len(arena.nodes):
                        raise ValueError("SLP fold child is invalid")
                    if child in remaining_uses:
                        previous = remaining_uses[child]
                        child_color = previous % 3
                        if child_color == 1:
                            raise ValueError("SLP fold grammar contains a cycle")
                        child_uses = previous // 3 + 1
                        remaining_uses[child] = child_uses * 3 + child_color
                        if child_color == 0:
                            if on_schedule is not None:
                                on_schedule(1)
                            tasks.append((child, False))
                    else:
                        if on_reference_entry is not None:
                            on_reference_entry(child)
                        remaining_uses[child] = 3
                        if on_schedule is not None:
                            on_schedule(1)
                        tasks.append((child, False))

        if on_schedule is not None:
            on_schedule(1)
        tasks.append((root, False))
        while tasks:
            node_id, ready = pop_task()
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
            if on_evaluate is not None:
                on_evaluate(node_id)
            children = ()
            if node.kind == "EMPTY":
                value = empty_value
            elif node.kind == "TERM":
                value = terminal_value(node.symbol)
            elif node.kind == "CONCAT":
                value = concatenate(values[node.left], values[node.right])
                children = (node.left, node.right)
            elif node.kind == "REPEAT":
                value = repeat(values[node.child], node.count)
                children = (node.child,)
            else:
                raise ValueError("unknown SLP node kind")
            values[node_id] = value
            if on_reduce is not None:
                on_reduce(node_id)
            if reclaim_values:
                for child in children:
                    reference_state = remaining_uses[child]
                    child_color = reference_state % 3
                    remaining = reference_state // 3
                    if child_color != 2 or remaining < 1:
                        raise AssertionError("SLP child reference count is invalid")
                    if remaining == 1:
                        del remaining_uses[child]
                        del values[child]
                        if on_reference_release is not None:
                            on_reference_release(child)
                        if on_value_release is not None:
                            on_value_release(child)
                    else:
                        remaining_uses[child] = (remaining - 1) * 3 + child_color
        if reclaim_values:
            if len(values) != 1 or root not in values or len(remaining_uses) != 1:
                raise AssertionError("SLP value reclamation did not reduce to its root")
            if remaining_uses[root] != 2:
                raise AssertionError("SLP root reference state is invalid")
            del remaining_uses[root]
            if on_reference_release is not None:
                on_reference_release(root)
        return values
    except BaseException as error:
        # Callback and reducer failures leave no partial graph pinned by the
        # retained traceback. Caller-owned reservations still unwind normally.
        pending_count = len(tasks)
        tasks.clear()
        try:
            if on_unschedule is not None and pending_count:
                on_unschedule(pending_count)
        except BaseException as cleanup_error:
            values.clear()
            remaining_uses.clear()
            value = empty_value
            raise cleanup_error from error
        values.clear()
        remaining_uses.clear()
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
