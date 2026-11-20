"""Immutable, bounded source classifier for compact future certificates.

This structure is candidate data only; it does not issue execution authority.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Final, NamedTuple

from number_compiler.sequences.comma.boundary_quotient import BoundaryState

RADICES: Final = (3, 4, 7, 11)
MAX_NODES: Final = 65_536


class SourceLeaf(NamedTuple):
    cid: int


class SourceBranch(NamedTuple):
    axis: int
    children: tuple[int, ...]


SourceNode = SourceLeaf | SourceBranch


class FutureSourceMDD(NamedTuple):
    """Topological MDD in N2..N9, Z2..Z9 root order."""

    nodes: tuple[SourceNode, ...]
    roots: tuple[int, ...]

    def validate(self, class_count: int) -> bool:
        """Check every node and require each class to occur in a reachable leaf."""
        if (
            type(class_count) is not int
            or class_count <= 0
            or type(self.nodes) is not tuple
            or not 0 < len(self.nodes) <= MAX_NODES
            or type(self.roots) is not tuple
            or len(self.roots) != 16
        ):
            return False
        for index, node in enumerate(self.nodes):
            if type(node) is SourceLeaf:
                if type(node.cid) is not int or node.cid < 0:
                    return False
            elif type(node) is SourceBranch:
                if (
                    type(node.axis) is not int
                    or not 0 <= node.axis < len(RADICES)
                    or type(node.children) is not tuple
                    or len(node.children) != RADICES[node.axis]
                ):
                    return False
                for child in node.children:
                    if type(child) is not int or not 0 <= child < index:
                        return False
                    child_node = self.nodes[child]
                    if (
                        type(child_node) is SourceBranch
                        and child_node.axis <= node.axis
                    ):
                        return False
            else:
                return False
        if any(
            type(root) is not int or not 0 <= root < len(self.nodes)
            for root in self.roots
        ):
            return False
        reachable = set(self.roots)
        pending = list(self.roots)
        classes: set[int] = set()
        while pending:
            node = self.nodes[pending.pop()]
            if type(node) is SourceLeaf:
                if node.cid >= class_count:
                    return False
                classes.add(node.cid)
            elif type(node) is SourceBranch:
                for child in node.children:
                    if child not in reachable:
                        reachable.add(child)
                        pending.append(child)
            else:
                return False
        return len(classes) == class_count

    def lookup(
        self, source: BoundaryState, *, charge_work: Callable[[int], None] | None = None
    ) -> int:
        """Evaluate the source phase through at most four branch nodes."""
        if type(source) is not BoundaryState:
            raise ValueError("malformed comma boundary source state")
        # Revalidate fields: frozen records can still be forged with object.__setattr__.
        if (
            type(source.kind) is not str
            or source.kind not in ("N", "Z")
            or type(source.a) is not int
            or not 2 <= source.a <= 9
            or type(source.exponent_residue) is not int
            or not 0 <= source.exponent_residue < 924
        ):
            raise ValueError("malformed comma boundary source state")
        if type(self.roots) is not tuple or len(self.roots) != 16:
            raise ValueError("malformed future source roots")
        if type(self.nodes) is not tuple:
            raise ValueError("malformed future source nodes")
        index = self.roots[(0 if source.kind == "N" else 8) + source.a - 2]
        previous_axis = -1
        for _ in range(len(RADICES) + 1):
            if charge_work is not None:
                charge_work(1)
            if type(index) is not int or not 0 <= index < len(self.nodes):
                raise ValueError("future source root or child is out of range")
            node = self.nodes[index]
            if type(node) is SourceLeaf:
                if type(node.cid) is not int or node.cid < 0:
                    raise ValueError("malformed future source leaf")
                return node.cid
            if (
                type(node) is not SourceBranch
                or type(node.axis) is not int
                or not previous_axis < node.axis < len(RADICES)
                or type(node.children) is not tuple
                or len(node.children) != RADICES[node.axis]
            ):
                raise ValueError("malformed future source branch")
            previous_axis = node.axis
            child = node.children[source.exponent_residue % RADICES[node.axis]]
            if type(child) is not int or not 0 <= child < index:
                raise ValueError("future source child is not topologically ordered")
            index = child
        raise ValueError("future source path exceeds its axis bound")
