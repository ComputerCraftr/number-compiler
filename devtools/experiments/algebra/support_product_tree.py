"""Balanced modular product tree for logarithmic support/GCD localization.

Research utility only.  It separates reusable support extraction from the
special-number baby/giant evaluator so callers can locate the first nonunit
leaf without a linear GCD scan.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd


@dataclass(frozen=True, slots=True)
class SupportProductNode:
    """Balanced product tree used only for logarithmic support localization."""

    start: int
    stop: int
    product: int
    left: SupportProductNode | None = None
    right: SupportProductNode | None = None

    @property
    def leaf(self) -> bool:
        return self.stop - self.start == 1


def support_product_tree(
    values: tuple[int, ...], modulus: int
) -> tuple[SupportProductNode, int]:
    """Build an exact balanced product tree with exactly n-1 combines.

    The tree reuses the same value products needed for the final support GCD,
    so logarithmic localization does not add a second linear multiplication
    pass over the baby/giant outputs.
    """
    vals = tuple(int(v) % int(modulus) for v in values)
    if not vals:
        raise ValueError("support tree requires at least one value")
    modulus = int(modulus)

    leaves = [SupportProductNode(i, i + 1, vals[i]) for i in range(len(vals))]
    combines = 0
    level = leaves
    while len(level) > 1:
        nxt: list[SupportProductNode] = []
        for i in range(0, len(level), 2):
            if i + 1 >= len(level):
                nxt.append(level[i])
                continue
            left, right = level[i], level[i + 1]
            nxt.append(
                SupportProductNode(
                    left.start,
                    right.stop,
                    left.product * right.product % modulus,
                    left,
                    right,
                )
            )
            combines += 1
        level = nxt
    return level[0], combines


def first_supported_leaf(
    root: SupportProductNode,
    modulus: int,
    *,
    prefix_values: tuple[int, ...] | None = None,
    prefix_limit: int = 0,
) -> tuple[int, int, int]:
    """Return earliest supported leaf with constant-prefix + tree descent.

    A small prefix preserves the common early-bend case.  Once that prefix is
    proven clear, the product tree is searched *after* the prefix, so those
    GCDs are never repeated.  The remaining locator cost is O(log n).
    """
    modulus = int(modulus)
    calls = 0
    prefix = 0
    if prefix_values is not None:
        prefix = min(len(prefix_values), max(0, int(prefix_limit)))
        for index, value in enumerate(prefix_values[:prefix]):
            leaf_gcd = gcd(modulus, int(value))
            calls += 1
            if leaf_gcd > 1:
                return index, leaf_gcd, calls

    found: tuple[int, int] | None = None
    stack = [root]
    while stack and found is None:
        node = stack.pop()
        if node.stop <= prefix:
            continue
        if node.start >= prefix:
            node_gcd = gcd(modulus, int(node.product))
            calls += 1
            if node_gcd == 1:
                continue
            if node.leaf:
                found = (node.start, node_gcd)
                break
        if node.leaf:
            node_gcd = gcd(modulus, int(node.product))
            calls += 1
            if node_gcd > 1:
                found = (node.start, node_gcd)
            continue
        assert node.left is not None and node.right is not None
        stack.append(node.right)
        stack.append(node.left)

    if found is None:
        raise AssertionError((root.start, root.stop, modulus, prefix))
    return found[0], found[1], calls


__all__ = ["SupportProductNode", "first_supported_leaf", "support_product_tree"]
