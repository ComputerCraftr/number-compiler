"""Collatz event interpretations over the shared ordered Boolean grammar."""

from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.tiles.ordered_boolean_support import (
    OrderedBooleanSupport,
    OrderedBooleanSupportArena,
)


class PhysicalSupport(OrderedBooleanSupport):
    """Boolean tape node with the Collatz-specific affine ring observer."""

    __slots__ = ()

    @property
    def parity(self) -> bool | None:
        """Compatibility view of the canonical uniform-symbol summary."""
        return self.symbol

    @property
    def odd_ticks(self) -> int:
        """Number of physical odd-branch symbols in this ordered word."""
        return self.true_count

    def specialize(self, *, s: int, z: int, modulus: int) -> SkewTransfer[int]:
        """Evaluate the Collatz branch word in its demanded coefficient ring."""
        self.owner.validate(self)
        if self.owner.ledger is not None:
            raise RuntimeError(
                "production support specialization requires a charged workspace"
            )
        if any(type(value) is not int for value in (s, z, modulus)) or modulus < 2:
            raise ValueError("support specialization requires an integer ring")
        if any(value.bit_length() > 4096 for value in (s, z, modulus)):
            raise BlockContextBudgetExceeded("support coefficient precision exceeded")

        def multiply(left: int, right: int) -> int:
            return left * right % modulus

        def add(left: int, right: int) -> int:
            return (left + right) % modulus

        return self.fold(
            identity=SkewTransfer(1, 0, 1),
            false_atom=SkewTransfer(1, 0, z % modulus),
            true_atom=SkewTransfer(s % modulus, 1, 1),
            then=lambda left, right: left.then(right, multiply=multiply, add=add),
        )


class PhysicalSupportArena(OrderedBooleanSupportArena):
    """Boolean support arena with Collatz atoms and its certified cycle word."""

    _support_node_type = PhysicalSupport

    @property
    def even(self) -> PhysicalSupport:
        return cast(PhysicalSupport, self.false)

    @property
    def odd(self) -> PhysicalSupport:
        return cast(PhysicalSupport, self.true)

    def run(self, parity: bool, count: int) -> PhysicalSupport:
        return cast(PhysicalSupport, super().run(parity, count))

    def concat(
        self, first: OrderedBooleanSupport, second: OrderedBooleanSupport
    ) -> PhysicalSupport:
        return cast(PhysicalSupport, super().concat(first, second))

    def _join_physical(
        self, first: PhysicalSupport, second: PhysicalSupport
    ) -> PhysicalSupport:
        return cast(PhysicalSupport, self._join(first, second))

    def event(self, divisions: int) -> PhysicalSupport:
        return self.concat(self.odd, self.run(False, divisions))

    def _cycle_levels(
        self, bits: int
    ) -> list[tuple[PhysicalSupport, PhysicalSupport, PhysicalSupport]]:
        """Return the three phase rotations for each dyadic word width."""
        levels = [(self.odd, self.even, self.even)]
        for level in range(1, bits):
            previous = levels[-1]
            shift = (1 << (level - 1)) % 3
            levels.append(
                (
                    self._join_physical(previous[0], previous[shift]),
                    self._join_physical(previous[1], previous[(1 + shift) % 3]),
                    self._join_physical(previous[2], previous[(2 + shift) % 3]),
                )
            )
        return levels

    def _proved_cycle_prefix(self, count: int) -> PhysicalSupport:
        """Build the source-proved prefix of ``O E E`` in O(log count) nodes."""
        if type(count) is not int or count < 0:
            raise ValueError("Collatz cycle duration must be nonnegative")
        bits = count.bit_length()
        if bits > min(self.max_nodes, 16384):
            raise BlockContextBudgetExceeded("Collatz cycle precision exceeded")
        if not count:
            return cast(PhysicalSupport, self.identity)
        levels = self._cycle_levels(bits)
        phase = 0
        selected: list[PhysicalSupport] = []
        for level in range(bits - 1, -1, -1):
            width = 1 << level
            if count & width:
                selected.append(levels[level][phase])
                phase = (phase + width) % 3
        result = selected.pop()
        while selected:
            result = self._join_physical(selected.pop(), result)
        return result

    def _proved_collatz_cycle_prefix(self, count: int) -> PhysicalSupport:
        return self._proved_cycle_prefix(count)

    def _mixed_cycle_block(
        self,
        levels: list[tuple[PhysicalSupport, PhysicalSupport, PhysicalSupport]],
        level: int,
        false_prefix: int,
    ) -> PhysicalSupport:
        """Build one dyadic block crossing the E/``O E E`` seam."""
        phase = 0
        frames: list[tuple[PhysicalSupport | None, PhysicalSupport | None]] = []
        while level:
            half = 1 << (level - 1)
            if false_prefix >= half:
                frames.append((self.run(False, half), None))
                false_prefix -= half
            else:
                consumed = half - false_prefix
                frames.append((None, levels[level - 1][(phase + consumed) % 3]))
            level -= 1
        result = self.even if false_prefix else levels[0][phase]
        while frames:
            left, right = frames.pop()
            if left is not None:
                result = self._join_physical(left, result)
            else:
                assert right is not None
                result = self._join_physical(result, right)
        return result

    def _proved_power_two_tail(
        self, entry_ticks: int, cycle_ticks: int
    ) -> PhysicalSupport:
        """Build an even prefix followed by the proved ``O E E`` cycle tail."""
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
            return cast(PhysicalSupport, self.identity)
        levels = self._cycle_levels(bits)
        chunks: list[PhysicalSupport] = []
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
            result = self._join_physical(chunks.pop(), result)
        return result

    def _proved_collatz_power_two_tail(
        self, entry_ticks: int, cycle_ticks: int
    ) -> PhysicalSupport:
        return self._proved_power_two_tail(entry_ticks, cycle_ticks)


__all__ = ["PhysicalSupport", "PhysicalSupportArena"]
