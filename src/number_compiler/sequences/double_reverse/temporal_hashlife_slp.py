"""Pure validation helpers for the decimal temporal Hashlife SLP caches."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPNode, canonical_repeat_key


def _valid_decimal_node(arena: LedgerSLPArena, node_id: int) -> bool:
    """Check local decimal-SLP shape and strict topological child ordering."""
    if type(node_id) is not int or not 0 <= node_id < len(arena.nodes):
        return False
    node = arena.nodes[node_id]
    if type(node) is not SLPNode or type(node.id) is not int or node.id != node_id:
        return False
    if type(node.length) is not int or node.length < 0:
        return False
    if node.kind == "EMPTY":
        return node_id == arena.empty_id and node.length == 0
    if node.kind == "TERM":
        return node.length == 1 and type(node.symbol) is int and 0 <= node.symbol <= 9
    if node.kind == "CONCAT":
        return (
            type(node.left) is int
            and type(node.right) is int
            and 0 <= node.left < node_id
            and 0 <= node.right < node_id
            and node.left != arena.empty_id
            and node.right != arena.empty_id
            and node.length
            == arena.nodes[node.left].length + arena.nodes[node.right].length
        )
    if node.kind == "REPEAT":
        return (
            type(node.child) is int
            and 0 <= node.child < node_id
            and node.child != arena.empty_id
            and type(node.count) is int
            and node.count >= 2
            and arena.nodes[node.child].kind != "REPEAT"
            and node.length == arena.nodes[node.child].length * node.count
        )
    return False


def existingsymbol_at(
    arena: LedgerSLPArena,
    root: int,
    position: int,
    *,
    on_visit: Callable[[], None] | None = None,
) -> int | None:
    """Read a symbol only through a bounded, locally validated SLP path."""
    if not _valid_decimal_node(arena, root):
        return None
    if type(position) is not int or not 0 <= position < arena.nodes[root].length:
        return None
    node_id = root
    offset = position
    remaining = len(arena.nodes)
    while remaining:
        remaining -= 1
        if not _valid_decimal_node(arena, node_id):
            return None
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
            if child_length <= 0:
                return None
            offset %= child_length
            node_id = node.child
        else:
            return None
    return None


def existing_concat(arena: LedgerSLPArena, left: int, right: int) -> int | None:
    """Resolve a concat only when its canonical interned node already exists."""
    if left == arena.empty_id:
        return right
    if right == arena.empty_id:
        return left
    return arena.existing_concat(left, right)


def _existing_repeat(arena: LedgerSLPArena, child: int, count: int) -> int | None:
    """Resolve the arena's flattened repeat identity without publishing nodes."""
    if not _valid_decimal_node(arena, child):
        return None
    key = canonical_repeat_key(arena.nodes, arena.empty_id, child, count)
    if isinstance(key, int):
        return key
    return arena.existing_repeat_entry(key)


def _existing_concat_many(arena: LedgerSLPArena, roots: list[int]) -> int | None:
    row = [root for root in roots if root != arena.empty_id]
    if not row:
        return arena.empty_id
    while len(row) > 1:
        next_row: list[int] = []
        for index in range(0, len(row), 2):
            left = row[index]
            if index + 1 == len(row):
                next_row.append(left)
                continue
            joined = existing_concat(arena, left, row[index + 1])
            if joined is None:
                return None
            next_row.append(joined)
        row = next_row
    return row[0]


def existing_part(arena: LedgerSLPArena, root: int, begin: int, end: int) -> int | None:
    """Reconstruct the exact canonical result of a slice without mutation."""
    if not _valid_decimal_node(arena, root):
        return None
    source = arena.nodes[root]
    if not 0 <= begin <= end <= source.length:
        return None
    if begin == end:
        return arena.empty_id
    if begin == 0 and end == source.length:
        return root

    tasks: list[tuple[int, int, int]] = [(root, begin, end)]
    fragments: list[int] = []
    work_limit = max(64, 8 * len(arena.nodes))
    visited = 0
    while tasks:
        child, lo, hi = tasks.pop()
        visited += 1
        if visited > work_limit or not _valid_decimal_node(arena, child):
            return None
        current = arena.nodes[child]
        if not 0 <= lo <= hi <= current.length:
            return None
        if lo == hi:
            continue
        if lo == 0 and hi == current.length:
            fragments.append(child)
            continue
        if current.kind == "CONCAT":
            pivot = arena.nodes[current.left].length
            if hi > pivot:
                tasks.append((current.right, max(0, lo - pivot), hi - pivot))
            if lo < pivot:
                tasks.append((current.left, lo, min(hi, pivot)))
            continue
        if current.kind != "REPEAT":
            return None
        child_length = arena.nodes[current.child].length
        if child_length <= 0:
            return None
        first, first_pos = divmod(lo, child_length)
        last, last_pos = divmod(hi, child_length)
        if first == last:
            tasks.append((current.child, first_pos, last_pos))
            continue
        if last_pos:
            tasks.append((current.child, 0, last_pos))
        copies = last - first - int(first_pos != 0)
        if copies:
            repeated = _existing_repeat(arena, current.child, copies)
            if repeated is None:
                return None
            tasks.append((repeated, 0, copies * child_length))
        if first_pos:
            tasks.append((current.child, first_pos, child_length))
    return _existing_concat_many(arena, fragments)


__all__ = ["existing_concat", "existing_part", "existingsymbol_at"]
