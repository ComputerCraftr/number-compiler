"""Read-only uniformity observer with no global computational cache."""

from __future__ import annotations

from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile


def tile_uniform_symbol(tile: DyadicTile) -> int | None:
    """Read immutable summaries; transient traversal also supports manual tiles."""
    expected: int | None = None
    visited: set[DyadicTile] = set()
    stack = [tile]
    while stack:
        node = stack.pop()
        if node in visited:
            continue
        visited.add(node)
        if node.symbol is not None:
            if expected is not None and expected != node.symbol:
                return None
            expected = node.symbol
            continue
        if node.left is None or node.right is None:
            raise AssertionError(node)
        stack.extend((node.left, node.right))
    return expected


__all__ = ["tile_uniform_symbol"]
