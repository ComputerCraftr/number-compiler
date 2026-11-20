"""Small iterative queries over straight-line-program grammars."""

from __future__ import annotations

from collections.abc import Callable, Generator
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_interval import SLPNodeArena
from number_compiler.resources.owned_memo import LedgerReservation

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger

_TaskObserver = Callable[[bool], None]
_ReserveTask = Callable[[], None]
_ReleaseTasks = Callable[[int], None]


def symbol_at(
    arena: SLPNodeArena,
    root: int,
    position: int,
    *,
    on_visit: Callable[[], None] | None = None,
) -> int:
    """Read one symbol without expanding repeated grammar regions."""
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise IndexError(root)
    if type(position) is not int or not 0 <= position < arena.nodes[root].length:
        raise IndexError(position)
    node_id = root
    offset = position
    while True:
        if on_visit is not None:
            on_visit()
        node = arena.nodes[node_id]
        if node.kind == "TERM":
            return node.symbol
        if node.kind == "CONCAT":
            left_length = arena.nodes[node.left].length
            if offset < left_length:
                node_id = node.left
            else:
                offset -= left_length
                node_id = node.right
        elif node.kind == "REPEAT":
            child_length = arena.nodes[node.child].length
            if child_length == 0:
                raise IndexError(position)
            offset %= child_length
            node_id = node.child
        elif node.kind == "EMPTY":
            raise ValueError("cannot read a symbol from an empty SLP node")
        else:
            raise ValueError(f"unknown SLP node kind: {node.kind}")


def iter_symbols(
    arena: SLPNodeArena,
    root: int,
    *,
    reverse: bool = False,
    on_task: _TaskObserver | None = None,
    reserve_task: _ReserveTask | None = None,
    release_tasks: _ReleaseTasks | None = None,
    ledger: ResourceLedger | None = None,
    owner: int | None = None,
    task_entries: int = 1,
    check_open: Callable[[], None] | None = None,
) -> Generator[int, None, None]:
    """Stream a grammar in either direction with ledger-owned traversal tasks.

    ``on_task`` receives ``True`` for a grammar-node visit and ``False`` for a
    repeat-continuation task. Callers can therefore preserve their own metric
    units while sharing traversal order and cleanup. Every retained stack item
    is reserved before insertion and released on pop or generator close.
    """
    if check_open is not None:
        check_open()
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise IndexError(root)

    reservation: LedgerReservation | None = None
    if ledger is not None and owner is not None:
        if reserve_task is not None or release_tasks is not None:
            raise ValueError("SLP walk cannot mix reservation and task callbacks")
        if type(task_entries) is not int or task_entries not in (0, 1):
            raise ValueError("SLP task entry charge must be zero or one")
        reservation = LedgerReservation(ledger, owner)

        def reserve_owned_task() -> None:
            assert reservation is not None
            reservation.reserve(entries=task_entries, nodes=1)

        def release_owned_tasks(count: int) -> None:
            assert reservation is not None
            reservation.release(entries=task_entries * count, nodes=count)

        reserve_task = reserve_owned_task
        release_tasks = release_owned_tasks
    elif ledger is not None or owner is not None:
        raise ValueError("SLP walk requires both ledger and owner")
    if reserve_task is None or release_tasks is None:
        raise ValueError("SLP walk requires a task reservation")

    tasks: list[tuple[str, int, int]] = []
    retained = 0

    def push(kind: str, node_id: int, count: int) -> None:
        nonlocal retained
        reserve_task()
        try:
            tasks.append((kind, node_id, count))
        except BaseException as error:
            try:
                release_tasks(1)
            except BaseException as cleanup_error:
                raise error from cleanup_error
            raise
        retained += 1

    try:
        push("node", root, 1)
        while True:
            if check_open is not None:
                check_open()
            if not tasks:
                break
            kind, node_id, count = tasks[-1]
            release_tasks(1)
            tasks.pop()
            retained -= 1
            if on_task is not None:
                on_task(kind == "node")
            if kind == "repeat":
                if count:
                    push("repeat", node_id, count - 1)
                    push("node", node_id, 1)
                continue
            if kind != "node":
                raise ValueError(f"unknown SLP traversal task: {kind}")
            node = arena.nodes[node_id]
            if node.kind == "EMPTY":
                continue
            if node.kind == "TERM":
                yield node.symbol
            elif node.kind == "CONCAT":
                first, second = (
                    (node.left, node.right) if reverse else (node.right, node.left)
                )
                push("node", first, 1)
                push("node", second, 1)
            elif node.kind == "REPEAT":
                if node.count:
                    push("repeat", node.child, node.count - 1)
                    push("node", node.child, 1)
            else:
                raise ValueError(f"unknown SLP node kind: {node.kind}")
    finally:
        if reservation is not None:
            tasks.clear()
            retained = 0
            try:
                reservation.retire()
            except BaseException as error:
                try:
                    reservation.close()
                except BaseException as cleanup_error:
                    raise error from cleanup_error
                raise
        else:
            try:
                if retained:
                    release_tasks(retained)
            finally:
                tasks.clear()
                retained = 0
