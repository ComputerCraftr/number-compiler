"""Ordered physical support for source-bound production and research constructors.

This is a bounded program arena, not by itself a source-to-program constructor. Endpoint
and clock equality do not erase this program. Ring observations and physical
selection read it without expanding its word or evaluating a Collatz source.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass, field
from typing import cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.arithmetic.functions.word_concatenation import concatenate_words
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True, eq=False)
class PhysicalSupport:
    owner: PhysicalSupportArena = field(repr=False)
    node_id: int
    ticks: int
    odd_ticks: int
    parity: bool | None
    left: PhysicalSupport | None = None
    right: PhysicalSupport | None = None

    def tick(self, index: int) -> bool:
        """Weighted selection from the same ordered support grammar."""
        self.owner.validate(self)
        if type(index) is not int or not 0 <= index < self.ticks:
            raise ValueError("physical support index is outside the program")
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
        assert node.parity is not None
        return node.parity

    def specialize(self, *, s: int, z: int, modulus: int) -> SkewTransfer[int]:
        """Evaluate the ordered support in a demanded finite coefficient ring."""
        self.owner.validate(self)
        if self.owner.ledger is not None:
            raise RuntimeError(
                "production support specialization requires a charged workspace"
            )
        if any(type(v) is not int for v in (s, z, modulus)) or modulus < 2:
            raise ValueError("support specialization requires an integer ring")
        if any(v.bit_length() > 4096 for v in (s, z, modulus)):
            raise BlockContextBudgetExceeded("support coefficient precision exceeded")
        values: dict[int, SkewTransfer[int]] = {}
        pending = [(self, False)]
        while pending:
            node, ready = pending.pop()
            self.owner.validate(node)
            if node.node_id in values:
                continue
            if not node.ticks:
                value = SkewTransfer(1, 0, 1)
            elif node.left is None:
                value = (
                    SkewTransfer(s % modulus, 1, 1)
                    if node.parity
                    else SkewTransfer(1, 0, z % modulus)
                )
            else:
                assert node.right is not None
                if not ready:
                    pending.extend(
                        ((node, True), (node.right, False), (node.left, False))
                    )
                    continue
                value = values[node.left.node_id].then(
                    values[node.right.node_id],
                    multiply=lambda a, b: a * b % modulus,
                    add=lambda a, b: (a + b) % modulus,
                )
            values[node.node_id] = value
        return values[self.node_id]


class PhysicalSupportArena:
    """Hash-consed ordered binary programs for physical tick words.

    Counts are derived at construction; only atoms and canonical child handles
    identify programs. General concatenation uses largest-dyadic-prefix normal
    form; the certified Collatz tail has one fixed source seam. Neither a
    coefficient specialization nor an endpoint is a key. The constructor has a
    separate explicit retained-node/work budget.
    """

    def __init__(self, *, max_nodes: int, ledger: ResourceLedger | None = None) -> None:
        if type(max_nodes) is not int or max_nodes < 3:
            raise ValueError("support node budget must admit identity and two atoms")
        self.max_nodes = max_nodes
        self.ledger = ledger
        # Research callers retain the uncharged specialization API, but their
        # persistent stores still come from a private ledger factory.
        self._store_ledger = ledger if ledger is not None else ResourceLedger()
        prefix = f"physical-support-{len(self._store_ledger.inventory())}"
        self._node_owner = self._store_ledger.register(
            prefix + "-nodes", "physical_shadow_support"
        )
        self._join_owner = self._store_ledger.register(
            prefix + "-joins", "physical_shadow_support_composition"
        )
        self._concat_owner = self._store_ledger.register(
            prefix + "-normalization", "physical_shadow_support_composition"
        )
        self._nodes: MutableSequence[PhysicalSupport] = self._store_ledger.make_list(
            self._node_owner
        )
        self._joins: MutableMapping[tuple[int, int], PhysicalSupport] = (
            self._store_ledger.make_dict(self._join_owner)
        )
        self._concats: MutableMapping[tuple[int, int], PhysicalSupport] = (
            self._store_ledger.make_dict(self._concat_owner)
        )
        self._store_ledger.register_execution_root(self)
        self.identity = self._new(0, 0, None)
        self.even = self._new(1, 0, False)
        self.odd = self._new(1, 1, True)
        self.compositions = 0
        self.intern_hits = 0

    def _new(
        self,
        ticks: int,
        odd_ticks: int,
        parity: bool | None,
        left: PhysicalSupport | None = None,
        right: PhysicalSupport | None = None,
        *,
        reserved: bool = False,
    ) -> PhysicalSupport:
        if len(self._nodes) >= self.max_nodes:
            raise BlockContextBudgetExceeded("physical support node budget exceeded")
        if not reserved:
            self._store_ledger.reserve(self._node_owner, entries=1, nodes=1)
        node = PhysicalSupport(
            self, len(self._nodes), ticks, odd_ticks, parity, left, right
        )
        self._nodes.append(node)
        return node

    def validate(self, node: PhysicalSupport) -> None:
        if (
            type(node) is not PhysicalSupport
            or node.owner is not self
            or type(node.node_id) is not int
            or not 0 <= node.node_id < len(self._nodes)
            or self._nodes[node.node_id] is not node
        ):
            raise ValueError("physical support belongs to another arena")
        expected: tuple[
            int,
            int,
            bool | None,
            PhysicalSupport | None,
            PhysicalSupport | None,
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
                type(left) is not PhysicalSupport
                or type(right) is not PhysicalSupport
                or left.owner is not self
                or right.owner is not self
                or self._joins.get((left.node_id, right.node_id)) is not node
            ):
                raise ValueError("physical support has a forged child program")
            a, b = left.parity, right.parity
            expected = (
                left.ticks + right.ticks,
                left.odd_ticks + right.odd_ticks,
                a if a == b else None,
                left,
                right,
            )
        if (node.ticks, node.odd_ticks, node.parity, node.left, node.right) != expected:
            raise ValueError("physical support semantic fields were modified")

    def _join(self, left: PhysicalSupport, right: PhysicalSupport) -> PhysicalSupport:
        key = left.node_id, right.node_id
        self.compositions += 1
        found = self._joins.get(key)
        if found is not None:
            self.intern_hits += 1
            return found
        a, b = left.parity, right.parity
        self._store_ledger.reserve_many(
            (
                (self._node_owner, 1, 1),
                (self._join_owner, 1, 0),
            )
        )
        try:
            node = self._new(
                left.ticks + right.ticks,
                left.odd_ticks + right.odd_ticks,
                a if a == b else None,
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

    def run(self, parity: bool, count: int) -> PhysicalSupport:
        if type(parity) is not bool or type(count) is not int or count < 0:
            raise ValueError("support run requires a parity and nonnegative duration")
        if count.bit_length() > min(self.max_nodes, 16384):
            raise BlockContextBudgetExceeded("support duration precision exceeded")
        if not count:
            return self.identity
        block = self.odd if parity else self.even
        selected = []
        while count:
            if count & 1:
                selected.append(block)
            count >>= 1
            if count:
                block = self._join(block, block)
        result = selected[0]
        for block in selected[1:]:
            result = self._join(block, result)
        return result

    def concat(
        self, first: PhysicalSupport, second: PhysicalSupport
    ) -> PhysicalSupport:
        self.validate(first)
        self.validate(second)

        reservations = 0

        def reserve() -> None:
            nonlocal reservations
            if len(self._concats) >= self.max_nodes:
                raise BlockContextBudgetExceeded(
                    "physical support join budget exceeded"
                )
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
                    cast(PhysicalSupport, node.left),
                    cast(PhysicalSupport, node.right),
                ),
                uniform=lambda node: node.parity,
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

    def event(self, divisions: int) -> PhysicalSupport:
        return self.concat(self.odd, self.run(False, divisions))

    def _collatz_cycle_levels(
        self, bits: int
    ) -> list[tuple[PhysicalSupport, PhysicalSupport, PhysicalSupport]]:
        """Return the three phase rotations for every demanded dyadic width."""
        levels = [(self.odd, self.even, self.even)]
        for level in range(1, bits):
            previous = levels[-1]
            shift = (1 << (level - 1)) % 3
            levels.append(
                (
                    self._join(previous[0], previous[shift]),
                    self._join(previous[1], previous[(1 + shift) % 3]),
                    self._join(previous[2], previous[(2 + shift) % 3]),
                )
            )
        return levels

    def _proved_collatz_cycle_prefix(self, count: int) -> PhysicalSupport:
        """Build the source-proved prefix of ``O E E`` in O(log count) nodes."""
        if type(count) is not int or count < 0:
            raise ValueError("Collatz cycle duration must be nonnegative")
        bits = count.bit_length()
        if bits > min(self.max_nodes, 16384):
            raise BlockContextBudgetExceeded("Collatz cycle precision exceeded")
        if not count:
            return self.identity

        # levels[k][p] is the exact 2**k-tick word beginning at cycle phase p.
        # Only the three rotations exist at each level; no caller-supplied word
        # can enter this source-certified constructor.
        levels = self._collatz_cycle_levels(bits)

        phase = 0
        selected = []
        for level in range(bits - 1, -1, -1):
            width = 1 << level
            if count & width:
                selected.append(levels[level][phase])
                phase = (phase + width) % 3
        result = selected.pop()
        while selected:
            result = self._join(selected.pop(), result)
        return result

    def _mixed_cycle_block(
        self,
        levels: list[tuple[PhysicalSupport, PhysicalSupport, PhysicalSupport]],
        level: int,
        even_prefix: int,
    ) -> PhysicalSupport:
        """Build one canonical dyadic block crossed by the E/cycle seam."""
        phase = 0
        frames: list[tuple[PhysicalSupport | None, PhysicalSupport | None]] = []
        while level:
            half = 1 << (level - 1)
            if even_prefix >= half:
                frames.append((self.run(False, half), None))
                even_prefix -= half
            else:
                consumed = half - even_prefix
                frames.append((None, levels[level - 1][(phase + consumed) % 3]))
            level -= 1
        result = self.even if even_prefix else levels[0][phase]
        while frames:
            left, right = frames.pop()
            if left is not None:
                result = self._join(left, result)
            else:
                assert right is not None
                result = self._join(result, right)
        return result

    def _proved_collatz_power_two_tail(
        self, entry_ticks: int, cycle_ticks: int
    ) -> PhysicalSupport:
        """Build ``E**entry_ticks`` followed by the proved ``O E E`` tail."""
        if (
            type(entry_ticks) is not int
            or type(cycle_ticks) is not int
            or entry_ticks < 0
            or cycle_ticks < 0
        ):
            raise ValueError("Collatz tail durations must be nonnegative")
        total = entry_ticks + cycle_ticks
        bits = total.bit_length()
        if bits > min(self.max_nodes, 16384):
            raise BlockContextBudgetExceeded("Collatz tail precision exceeded")
        if not total:
            return self.identity
        levels = self._collatz_cycle_levels(bits)
        chunks = []
        offset = 0
        for level in range(bits - 1, -1, -1):
            width = 1 << level
            if not total & width:
                continue
            end = offset + width
            if end <= entry_ticks:
                chunk = self.run(False, width)
            elif offset >= entry_ticks:
                chunk = levels[level][(offset - entry_ticks) % 3]
            else:
                chunk = self._mixed_cycle_block(levels, level, entry_ticks - offset)
            chunks.append(chunk)
            offset = end
        result = chunks.pop()
        while chunks:
            result = self._join(chunks.pop(), result)
        return result

    @property
    def node_count(self) -> int:
        return len(self._nodes)
