"""Exact spatial fold of a supplied binary SLP modulo ``2**w + 1``.

The fold is compositional over the shared SLP DAG. It observes a complete
caller-owned word; it does not construct ``3**(2**t)`` from a clock or decide
primality.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.sequences.power_numbers.fermat_signed_reducer import (
    MAX_FERMAT_FOLD_WIDTH,
    fold_signed_fermat,
)

MAX_BINARY_SLP_NODES = 65_536
MAX_SLP_INTEGER_BITS = 4_096


@dataclass(frozen=True, slots=True, init=False)
class FermatBinarySLPSnapshot:
    """Bounded immutable copy of one admitted binary SLP root."""

    nodes: tuple[SLPNode, ...]
    root: int
    one_counts: tuple[int, ...]

    @classmethod
    def admit(
        cls,
        arena: SLPArena,
        root: int,
        *,
        max_nodes: int = MAX_BINARY_SLP_NODES,
    ) -> FermatBinarySLPSnapshot:
        """Validate once and copy only the reachable child-first source DAG."""
        if type(arena) is not SLPArena:
            raise TypeError("binary source admission requires an exact SLPArena")
        root = require_integer(root, "binary source root", 0)
        if root >= len(arena.nodes):
            raise ValueError("binary source root is invalid")
        max_nodes = require_integer(
            max_nodes, "binary source node budget", 1, MAX_BINARY_SLP_NODES
        )

        reachable: set[int] = set()
        pending = [root]
        while pending:
            node_id = pending.pop()
            if node_id in reachable:
                continue
            if not 0 <= node_id < len(arena.nodes):
                raise ValueError("binary SLP contains a foreign child handle")
            if len(reachable) >= max_nodes:
                raise ValueError(("binary-source-node-budget", max_nodes))
            node = arena.nodes[node_id]
            if type(node) is not SLPNode or node.id != node_id:
                raise ValueError("binary SLP node identity is stale or malformed")
            _validate_node_shape(node)
            reachable.add(node_id)
            if node.kind == "CONCAT":
                left = _checked_child(arena, node.left)
                right = _checked_child(arena, node.right)
                if (
                    left.length > node.length
                    or right.length != node.length - left.length
                ):
                    raise ValueError("concat SLP length is inconsistent")
                pending.extend((node.right, node.left))
            elif node.kind == "REPEAT":
                child = _checked_child(arena, node.child)
                if child.length == 0:
                    consistent = node.length == 0
                else:
                    count, remainder = divmod(node.length, child.length)
                    consistent = remainder == 0 and count == node.count
                if not consistent:
                    raise ValueError("repeat SLP length is inconsistent")
                pending.append(node.child)

        ordered_ids = sorted(reachable)
        remap = {old: new for new, old in enumerate(ordered_ids)}
        compact: list[SLPNode] = []
        one_counts: list[int] = []
        for old_id in ordered_ids:
            node = arena.nodes[old_id]
            if node.kind == "TERM" and node.symbol not in (0, 1):
                raise ValueError("Fermat binary source terminals must be 0 or 1")
            if node.kind == "CONCAT":
                compact.append(
                    SLPNode(
                        len(compact),
                        node.kind,
                        node.length,
                        left=remap[node.left],
                        right=remap[node.right],
                    )
                )
                one_counts.append(
                    one_counts[remap[node.left]] + one_counts[remap[node.right]]
                )
            elif node.kind == "REPEAT":
                compact.append(
                    SLPNode(
                        len(compact),
                        node.kind,
                        node.length,
                        child=remap[node.child],
                        count=node.count,
                    )
                )
                one_counts.append(one_counts[remap[node.child]] * node.count)
            elif node.kind == "TERM":
                compact.append(
                    SLPNode(len(compact), node.kind, node.length, symbol=node.symbol)
                )
                one_counts.append(node.symbol)
            else:
                compact.append(SLPNode(len(compact), node.kind, node.length))
                one_counts.append(0)
        snapshot = object.__new__(cls)
        object.__setattr__(snapshot, "nodes", tuple(compact))
        object.__setattr__(snapshot, "root", remap[root])
        object.__setattr__(snapshot, "one_counts", tuple(one_counts))
        return snapshot

    def count_ones(
        self, begin: int, end: int, *, max_visits: int = MAX_BINARY_SLP_NODES
    ) -> tuple[int, int]:
        """Return a bounded interval one-count and the visits it consumed."""
        length = self.nodes[self.root].length
        begin = require_integer(begin, "binary source interval start", 0)
        end = require_integer(end, "binary source interval end", begin)
        if end > length:
            raise ValueError(("binary-source-interval", begin, end, length))
        max_visits = require_integer(
            max_visits, "binary source interval budget", 1, MAX_BINARY_SLP_NODES
        )
        if begin == end:
            return 0, 0
        visits = 0

        def visit() -> None:
            nonlocal visits
            visits += 1
            if visits > max_visits:
                raise ValueError(("binary-source-interval-budget", max_visits))

        values = fold_slp_interval(
            self,
            self.root,
            begin,
            end,
            identity=(0, 0),
            length=lambda node_id: self.nodes[node_id].length,
            full_value=lambda node_id, _reverse: (
                self.nodes[node_id].length,
                self.one_counts[node_id],
            ),
            compose=lambda lower, higher: (
                lower[0] + higher[0],
                lower[1] + higher[1],
            ),
            repeat=lambda block, count: (block[0] * count, block[1] * count),
            on_visit=visit,
        )
        return values[1], visits

    def fold(
        self, *, width: int, max_nodes: int = MAX_BINARY_SLP_NODES
    ) -> FermatBinaryFoldAction:
        selected_width = _width(width)
        max_nodes = require_integer(
            max_nodes, "binary source node budget", 1, MAX_BINARY_SLP_NODES
        )
        reduced = 0

        def on_reduce(_node_id: int) -> None:
            nonlocal reduced
            reduced += 1
            if reduced > max_nodes:
                raise ValueError(("binary-source-fold-budget", max_nodes))

        values = fold_slp_dag(
            self,
            self.root,
            empty_value=FermatBinaryFoldAction.identity(selected_width),
            terminal_value=lambda digit: FermatBinaryFoldAction.digit(
                selected_width, digit
            ),
            concatenate=lambda lower, higher: lower.then(higher),
            repeat=lambda block, count: block.repeat(count),
            on_reduce=on_reduce,
        )
        action = values[self.root]
        if action.length != self.nodes[self.root].length:
            raise ArithmeticError("Fermat fold lost the source SLP length")
        return action


def _validate_node_shape(node: SLPNode) -> None:
    if type(node.kind) is not str:
        raise ValueError("binary SLP node kind must be an exact string")
    exact_fields = (
        node.id,
        node.length,
        node.symbol,
        node.left,
        node.right,
        node.child,
        node.count,
    )
    if any(type(value) is not int for value in exact_fields):
        raise ValueError("binary SLP node fields must be exact integers")
    if node.length < 0 or node.length.bit_length() > MAX_SLP_INTEGER_BITS:
        raise ValueError("binary SLP source length exceeds its exact budget")
    if node.kind == "EMPTY":
        if node.length != 0:
            raise ValueError("empty SLP node has nonzero length")
    elif node.kind == "TERM":
        if node.length != 1:
            raise ValueError("terminal SLP node has invalid length")
    elif node.kind == "CONCAT":
        if not (0 <= node.left < node.id and 0 <= node.right < node.id):
            raise ValueError("concat SLP child is stale or cyclic")
        if node.length.bit_length() > MAX_SLP_INTEGER_BITS:
            raise ValueError("binary SLP source horizon exceeds its exact budget")
    elif node.kind == "REPEAT":
        if not 0 <= node.child < node.id or node.count < 0:
            raise ValueError("repeat SLP child or count is invalid")
        if node.count.bit_length() > MAX_SLP_INTEGER_BITS:
            raise ValueError("binary SLP repeat count exceeds its exact budget")
    else:
        raise ValueError("unknown binary SLP node kind")


def _checked_child(arena: SLPArena, node_id: int) -> SLPNode:
    child = arena.nodes[node_id]
    if type(child) is not SLPNode or child.id != node_id:
        raise ValueError("binary SLP child handle is stale or malformed")
    _validate_node_shape(child)
    return child


def _width(value: int) -> int:
    if type(value) is not int or not 1 <= value <= MAX_FERMAT_FOLD_WIDTH:
        raise ValueError(("fermat-fold-width-budget", value, MAX_FERMAT_FOLD_WIDTH))
    return value


@dataclass(frozen=True, slots=True)
class FermatBinaryFoldAction:
    """Exact residue summary for an LSD-first binary word."""

    width: int
    length: int
    residue: int

    def __post_init__(self) -> None:
        width = _width(self.width)
        if type(self.length) is not int or self.length < 0:
            raise ValueError("binary source length must be a nonnegative exact integer")
        if type(self.residue) is not int or not 0 <= self.residue <= (1 << width):
            raise ValueError("residue is outside the canonical Fermat range")

    @property
    def modulus(self) -> int:
        return (1 << self.width) + 1

    @property
    def phase(self) -> int:
        """Alternating block phase, independent of represented word length."""
        return self.length % (2 * self.width)

    @classmethod
    def identity(cls, width: int) -> FermatBinaryFoldAction:
        return cls(_width(width), 0, 0)

    @classmethod
    def digit(cls, width: int, digit: int) -> FermatBinaryFoldAction:
        if type(digit) is not int or digit not in (0, 1):
            raise ValueError("binary Fermat fold accepts exact 0/1 terminals")
        return cls(_width(width), 1, digit)

    def then(self, higher: FermatBinaryFoldAction) -> FermatBinaryFoldAction:
        """Append the more-significant source block without expansion."""
        if type(higher) is not FermatBinaryFoldAction or self.width != higher.width:
            raise ValueError("Fermat fold actions require matching widths")
        quotient, remainder = divmod(self.phase, self.width)
        shift = (1 << remainder) * (-1 if quotient else 1)
        residue = fold_signed_fermat(self.residue + shift * higher.residue, self.width)
        return FermatBinaryFoldAction(self.width, self.length + higher.length, residue)

    def repeat(self, count: int) -> FermatBinaryFoldAction:
        """Compose one repeated block by binary powering of this finite action."""
        selected_count = require_integer(count, "Fermat action repeat count", 0)
        if selected_count.bit_length() > MAX_SLP_INTEGER_BITS:
            raise ValueError("Fermat action repeat count exceeds its exact budget")

        def compose(
            first: FermatBinaryFoldAction, second: FermatBinaryFoldAction
        ) -> FermatBinaryFoldAction:
            return first.then(second)

        return binary_power(
            self,
            selected_count,
            identity=self.identity(self.width),
            compose=compose,
        ).value

    @property
    def terminal_is_minus_one(self) -> bool:
        """A residue observation only; source completeness must come elsewhere."""
        return self.residue == self.modulus - 1


def fold_binary_slp(
    arena: SLPArena,
    root: int,
    *,
    width: int,
    max_nodes: int = MAX_BINARY_SLP_NODES,
) -> FermatBinaryFoldAction:
    """Fold a supplied ``EMPTY/TERM/CONCAT/REPEAT`` binary SLP without decoding."""
    return FermatBinarySLPSnapshot.admit(arena, root, max_nodes=max_nodes).fold(
        width=width, max_nodes=max_nodes
    )


__all__ = [
    "FermatBinaryFoldAction",
    "FermatBinarySLPSnapshot",
    "fold_binary_slp",
]
