"""Ledger-owned HashLife grammar for ordered Boolean labels.

This owner handles only the word structure, exact symbol counts, and weighted
selection. Family recurrence laws and ring interpretations belong to the
family that supplies or observes the tape.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping, MutableSequence
from dataclasses import dataclass, field
from typing import TypeVar, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.morphism_core import canonical_uniform_power
from number_compiler.arithmetic.functions.word_concatenation import concatenate_words
from number_compiler.resources.ledger import ResourceLedger

T = TypeVar("T")


@dataclass(frozen=True, slots=True, eq=False)
class OrderedBooleanSupport:
    """One node in a canonical ordered Boolean support grammar."""

    owner: OrderedBooleanSupportArena = field(repr=False)
    node_id: int
    ticks: int
    true_count: int
    symbol: bool | None
    left: OrderedBooleanSupport | None = None
    right: OrderedBooleanSupport | None = None

    def tick(self, index: int) -> bool:
        """Select one Boolean symbol by its exact position."""
        self.owner.validate(self)
        if type(index) is not int or not 0 <= index < self.ticks:
            raise ValueError("support index is outside the Boolean word")
        node = self
        while node.left is not None:
            self.owner.validate(node)
            left, right = node.left, node.right
            assert right is not None
            if index < left.ticks:
                node = left
            else:
                index -= left.ticks
                node = right
        assert node.symbol is not None
        return node.symbol

    def fold(
        self,
        *,
        identity: T,
        false_atom: T,
        true_atom: T,
        then: Callable[[T, T], T],
    ) -> T:
        """Evaluate this word in a caller-supplied monoid without expansion."""
        self.owner.validate(self)
        values: dict[int, T] = {}
        pending = [(self, False)]
        while pending:
            node, ready = pending.pop()
            self.owner.validate(node)
            if node.node_id in values:
                continue
            if node.ticks == 0:
                value = identity
            elif node.left is None:
                assert node.symbol is not None
                value = true_atom if node.symbol else false_atom
            else:
                right = node.right
                assert right is not None
                if not ready:
                    pending.extend(((node, True), (right, False), (node.left, False)))
                    continue
                value = then(values[node.left.node_id], values[right.node_id])
            values[node.node_id] = value
        return values[self.node_id]


class OrderedBooleanSupportArena:
    """Hash-consed, budgeted constructors for ordered Boolean words."""

    _support_node_type = OrderedBooleanSupport

    def __init__(self, *, max_nodes: int, ledger: ResourceLedger | None = None) -> None:
        if type(max_nodes) is not int or max_nodes < 3:
            raise ValueError("support node budget must admit identity and two atoms")
        self.max_nodes = max_nodes
        self.ledger = ledger
        self._store_ledger = ledger if ledger is not None else ResourceLedger()
        prefix = f"ordered-boolean-support-{len(self._store_ledger.inventory())}"
        self._node_owner = self._store_ledger.register(
            prefix + "-nodes", "ordered_boolean_support"
        )
        self._join_owner = self._store_ledger.register(
            prefix + "-joins", "ordered_boolean_support_composition"
        )
        self._concat_owner = self._store_ledger.register(
            prefix + "-normalization", "ordered_boolean_support_composition"
        )
        self._nodes: MutableSequence[OrderedBooleanSupport] = (
            self._store_ledger.make_list(self._node_owner)
        )
        self._joins: MutableMapping[tuple[int, int], OrderedBooleanSupport] = (
            self._store_ledger.make_dict(self._join_owner)
        )
        self._concats: MutableMapping[tuple[int, int], OrderedBooleanSupport] = (
            self._store_ledger.make_dict(self._concat_owner)
        )
        self._store_ledger.register_execution_root(self)
        self.identity = self._new(0, 0, None)
        self.false = self._new(1, 0, False)
        self.true = self._new(1, 1, True)
        self.compositions = 0
        self.intern_hits = 0

    def _new(
        self,
        ticks: int,
        true_count: int,
        symbol: bool | None,
        left: OrderedBooleanSupport | None = None,
        right: OrderedBooleanSupport | None = None,
        *,
        reserved: bool = False,
    ) -> OrderedBooleanSupport:
        if len(self._nodes) >= self.max_nodes:
            raise BlockContextBudgetExceeded("support node budget exceeded")
        if not reserved:
            self._store_ledger.reserve(self._node_owner, entries=1, nodes=1)
        node = self._support_node_type(
            self, len(self._nodes), ticks, true_count, symbol, left, right
        )
        self._nodes.append(node)
        return node

    def validate(self, node: OrderedBooleanSupport) -> None:
        if (
            type(node) is not self._support_node_type
            or node.owner is not self
            or type(node.node_id) is not int
            or not 0 <= node.node_id < len(self._nodes)
            or self._nodes[node.node_id] is not node
        ):
            raise ValueError("Boolean support belongs to another arena")
        expected: tuple[
            int,
            int,
            bool | None,
            OrderedBooleanSupport | None,
            OrderedBooleanSupport | None,
        ]
        if node.node_id == 0:
            expected = (0, 0, None, None, None)
        elif node.node_id == 1:
            expected = (1, 0, False, None, None)
        elif node.node_id == 2:
            expected = (1, 1, True, None, None)
        else:
            left, right = node.left, node.right
            if (
                type(left) is not self._support_node_type
                or type(right) is not self._support_node_type
                or left.owner is not self
                or right.owner is not self
                or self._joins.get((left.node_id, right.node_id)) is not node
            ):
                raise ValueError("Boolean support has a forged child program")
            expected = (
                left.ticks + right.ticks,
                left.true_count + right.true_count,
                left.symbol if left.symbol == right.symbol else None,
                left,
                right,
            )
        if (
            node.ticks,
            node.true_count,
            node.symbol,
            node.left,
            node.right,
        ) != expected:
            raise ValueError("Boolean support semantic fields were modified")

    def _join(
        self, left: OrderedBooleanSupport, right: OrderedBooleanSupport
    ) -> OrderedBooleanSupport:
        key = left.node_id, right.node_id
        self.compositions += 1
        found = self._joins.get(key)
        if found is not None:
            self.intern_hits += 1
            return found
        self._store_ledger.reserve_many(
            ((self._node_owner, 1, 1), (self._join_owner, 1, 0))
        )
        try:
            node = self._new(
                left.ticks + right.ticks,
                left.true_count + right.true_count,
                left.symbol if left.symbol == right.symbol else None,
                left,
                right,
                reserved=True,
            )
        except BaseException:
            self._store_ledger.release(self._node_owner, entries=1, nodes=1)
            self._store_ledger.release(self._join_owner, entries=1)
            raise
        self._joins[key] = node
        return node

    def run(self, symbol: bool, count: int) -> OrderedBooleanSupport:
        if type(symbol) is not bool or type(count) is not int or count < 0:
            raise ValueError(
                "support run requires a Boolean symbol and nonnegative length"
            )
        if count.bit_length() > min(self.max_nodes, 16384):
            raise BlockContextBudgetExceeded("support duration precision exceeded")
        if not count:
            return self.identity
        atom = self.true if symbol else self.false
        return canonical_uniform_power(atom, count, compose=self._join)

    def concat(
        self,
        first: OrderedBooleanSupport,
        second: OrderedBooleanSupport,
    ) -> OrderedBooleanSupport:
        self.validate(first)
        self.validate(second)
        reservations = 0

        def reserve() -> None:
            nonlocal reservations
            if len(self._concats) >= self.max_nodes:
                raise BlockContextBudgetExceeded("support join budget exceeded")
            self._store_ledger.reserve(self._concat_owner, entries=1)
            reservations += 1

        previous = len(self._concats)
        try:
            result = concatenate_words(
                first,
                second,
                key_of=lambda node: node.node_id,
                length=lambda node: node.ticks,
                children=lambda node: (
                    cast(OrderedBooleanSupport, node.left),
                    cast(OrderedBooleanSupport, node.right),
                ),
                uniform=lambda node: node.symbol,
                run=self.run,
                join=self._join,
                cache=self._concats,
                reserve=reserve,
            )
        finally:
            retained = len(self._concats) - previous
            excess = reservations - retained
            if excess:
                self._store_ledger.release(self._concat_owner, entries=excess)
        return result

    @property
    def node_count(self) -> int:
        return len(self._nodes)


__all__ = ["OrderedBooleanSupport", "OrderedBooleanSupportArena"]
