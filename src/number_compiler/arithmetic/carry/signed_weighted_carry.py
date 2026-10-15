"""Budgeted weighted-block actions for signed binary carry normalization.

For an LSD-first coefficient block ``a_0, ..., a_(L-1)``, normalization
acts on an incoming carry by

    C(c) = floor((c + sum(a_i * 2**i)) / 2**L).

The weighted sum is retained compositionally over ``CONCAT`` and ``REPEAT``
SLP nodes. This is a spatial carry summary, not a source-authentication proof:
callers that use the result as a certificate must authenticate the coefficient
grammar separately.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at

MAX_SIGNED_CARRY_WIDTH = 65_536
MAX_SIGNED_WEIGHTED_BITS = 262_144


class SignedCarryBudgetExceeded(ValueError):
    """A requested signed carry action exceeds its explicit integer budget."""


def _budget(value: int, name: str, upper: int, *, minimum: int = 1) -> int:
    if type(value) is not int or not minimum <= value <= upper:
        raise SignedCarryBudgetExceeded((name, value, minimum, upper))
    return value


@dataclass(frozen=True, slots=True)
class WeightedCarryBlock:
    """Exact block action ``c -> floor((c + value) / 2**length)``."""

    length: int
    value: int

    def __post_init__(self) -> None:
        if type(self.length) is not int or self.length < 0:
            raise ValueError(("invalid-carry-block-length", self.length))
        if type(self.value) is not int:
            raise TypeError("weighted carry value must be an exact integer")

    def then(
        self,
        other: WeightedCarryBlock,
        *,
        max_length: int,
        max_weighted_bits: int = MAX_SIGNED_WEIGHTED_BITS,
    ) -> WeightedCarryBlock:
        """Concatenate two LSD-first blocks after preflighting allocation."""
        if type(other) is not WeightedCarryBlock:
            raise TypeError(type(other))
        width_budget = _budget(max_length, "carry-width-budget", MAX_SIGNED_CARRY_WIDTH)
        bits_budget = _budget(
            max_weighted_bits,
            "weighted-integer-budget",
            MAX_SIGNED_WEIGHTED_BITS,
            minimum=8,
        )
        length = self.length + other.length
        if length > width_budget:
            raise SignedCarryBudgetExceeded("carry block length exceeds budget")
        shifted_bits = other.value.bit_length() + self.length if other.value else 0
        result_upper_bits = max(self.value.bit_length(), shifted_bits) + 1
        if result_upper_bits > bits_budget:
            raise SignedCarryBudgetExceeded("exact weighted integer exceeds budget")
        value = self.value + (other.value << self.length)
        if value.bit_length() > bits_budget:
            raise SignedCarryBudgetExceeded("exact weighted integer exceeds budget")
        return WeightedCarryBlock(length, value)

    def power(
        self,
        count: int,
        *,
        max_length: int,
        max_weighted_bits: int = MAX_SIGNED_WEIGHTED_BITS,
    ) -> WeightedCarryBlock:
        """Compose a repeated block by binary powering."""
        if type(count) is not int or count < 0:
            raise ValueError(count)
        width_budget = _budget(max_length, "carry-width-budget", MAX_SIGNED_CARRY_WIDTH)
        bits_budget = _budget(
            max_weighted_bits,
            "weighted-integer-budget",
            MAX_SIGNED_WEIGHTED_BITS,
            minimum=8,
        )
        if self.length * count > width_budget:
            raise SignedCarryBudgetExceeded("repeat width exceeds budget")
        result = WeightedCarryBlock(0, 0)
        action = self
        remaining = count
        while remaining:
            if remaining & 1:
                result = result.then(
                    action,
                    max_length=width_budget,
                    max_weighted_bits=bits_budget,
                )
            remaining >>= 1
            if remaining:
                action = action.then(
                    action,
                    max_length=width_budget,
                    max_weighted_bits=bits_budget,
                )
        return result

    def apply(self, incoming: int) -> int:
        if type(incoming) is not int:
            raise TypeError("incoming carry must be an exact integer")
        return (incoming + self.value) >> self.length


class WideSignedCarryAction:
    """Exact signed seam and carry ports over an authenticated coefficient SLP.

    The SLP is summarized without expanding ``REPEAT`` nodes. This class
    assumes its integer coefficients are already source-authenticated; it
    checks normalization and the cyclic/negacyclic seam only.
    """

    def __init__(
        self,
        arena: SLPArena,
        root: int,
        *,
        sign: int,
        max_width: int = MAX_SIGNED_CARRY_WIDTH,
        max_weighted_bits: int = MAX_SIGNED_WEIGHTED_BITS,
    ) -> None:
        if not isinstance(arena, SLPArena):
            raise TypeError("a signed carry source must be an SLP arena")
        if type(root) is not int or not 0 <= root < len(arena.nodes):
            raise IndexError(root)
        if type(sign) is not int or sign not in (-1, 1):
            raise ValueError("signed seam must be +1 or -1")
        width_budget = _budget(max_width, "carry-width-budget", MAX_SIGNED_CARRY_WIDTH)
        bits_budget = _budget(
            max_weighted_bits,
            "weighted-integer-budget",
            MAX_SIGNED_WEIGHTED_BITS,
            minimum=8,
        )
        width = arena.nodes[root].length
        if not 1 <= width <= width_budget:
            raise SignedCarryBudgetExceeded("signed carry width exceeds budget")

        self.arena = arena
        self.root = root
        self.width = width
        self.sign = sign
        self.max_width = width_budget
        self.max_weighted_bits = bits_budget
        self._summaries: dict[int, WeightedCarryBlock] = {}
        for node_id in sorted(arena.reachable(root)):
            node = arena.nodes[node_id]
            if node.kind == "EMPTY":
                summary = WeightedCarryBlock(0, 0)
            elif node.kind == "TERM":
                if node.symbol.bit_length() > bits_budget:
                    raise SignedCarryBudgetExceeded(
                        "source coefficient exceeds weighted integer budget"
                    )
                summary = WeightedCarryBlock(1, node.symbol)
            elif node.kind == "CONCAT":
                summary = self._summaries[node.left].then(
                    self._summaries[node.right],
                    max_length=width_budget,
                    max_weighted_bits=bits_budget,
                )
            elif node.kind == "REPEAT":
                summary = self._summaries[node.child].power(
                    node.count,
                    max_length=width_budget,
                    max_weighted_bits=bits_budget,
                )
            else:  # pragma: no cover - arena invariant
                raise AssertionError(node.kind)
            self._summaries[node_id] = summary

        self.block = self._summaries[root]
        if self.block.length != width:
            raise ArithmeticError("SLP summary length mismatch")
        modulus = (1 << width) - sign
        residue = self.block.value % modulus
        self.residue = residue
        self.signed_minus_one = sign == -1 and residue == (1 << width)
        if self.signed_minus_one:
            self.c0 = -((self.block.value + 1) // modulus)
        elif sign == -1:
            self.c0 = -(self.block.value // modulus)
        else:
            # Cyclic residue zero has a second all-ones representation;
            # the canonical emitted word is all zeroes.
            self.c0 = self.block.value // modulus
        if self.carry_at(width) != sign * self.c0:
            raise ArithmeticError("cyclic/negacyclic signed seam did not close")

    def _prefix(self, count: int) -> WeightedCarryBlock:
        if type(count) is not int or not 0 <= count <= self.width:
            raise IndexError(count)
        q = self.root
        result = WeightedCarryBlock(0, 0)
        while count:
            node = self.arena.nodes[q]
            if count == node.length:
                return result.then(
                    self._summaries[q],
                    max_length=self.max_width,
                    max_weighted_bits=self.max_weighted_bits,
                )
            if node.kind == "CONCAT":
                left_length = self.arena.nodes[node.left].length
                if count <= left_length:
                    q = node.left
                else:
                    result = result.then(
                        self._summaries[node.left],
                        max_length=self.max_width,
                        max_weighted_bits=self.max_weighted_bits,
                    )
                    count -= left_length
                    q = node.right
            elif node.kind == "REPEAT":
                child_length = self.arena.nodes[node.child].length
                copies, count = divmod(count, child_length)
                if copies:
                    repeated = self._summaries[node.child].power(
                        copies,
                        max_length=self.max_width,
                        max_weighted_bits=self.max_weighted_bits,
                    )
                    result = result.then(
                        repeated,
                        max_length=self.max_width,
                        max_weighted_bits=self.max_weighted_bits,
                    )
                q = node.child
            else:  # pragma: no cover - partial terminal is impossible
                raise AssertionError(node.kind)
        return result

    def carry_at(self, boundary: int) -> int:
        """Signed carry entering a boundary, including both seam endpoints."""
        if type(boundary) is not int or not 0 <= boundary <= self.width:
            raise IndexError(boundary)
        prefix = self._prefix(boundary)
        incoming = self.c0 + int(self.signed_minus_one and boundary > 0)
        return prefix.apply(incoming)

    def digit_at(self, position: int) -> int:
        """Canonical output digit, including signed ``-1`` at the exception."""
        if type(position) is not int or not 0 <= position < self.width:
            raise IndexError(position)
        if self.signed_minus_one and position == 0:
            return -1
        return (
            symbol_at(self.arena, self.root, position) + self.carry_at(position)
        ) & 1

    def verify_cochain(self) -> bool:
        """Check every integer carry equation and the signed terminal seam."""
        carry = self.c0
        for position in range(self.width):
            coefficient = symbol_at(self.arena, self.root, position)
            digit = self.digit_at(position)
            numerator = coefficient + carry - digit
            if numerator & 1:
                return False
            carry = numerator // 2
            if carry != self.carry_at(position + 1):
                return False
        return carry == self.sign * self.c0

    def demand(self, positions: tuple[int, ...]) -> tuple[tuple[int, int, int], ...]:
        """Return ``(position, output digit, incoming carry)`` at requested cells."""
        if type(positions) is not tuple:
            raise ValueError("positions must be an immutable tuple")
        if len(positions) > self.width:
            raise ValueError("position demand exceeds action width")
        if any(type(i) is not int or not 0 <= i < self.width for i in positions):
            raise IndexError(positions)
        if len(set(positions)) != len(positions):
            raise ValueError("positions must be unique")
        return tuple((i, self.digit_at(i), self.carry_at(i)) for i in positions)


__all__ = [
    "MAX_SIGNED_CARRY_WIDTH",
    "MAX_SIGNED_WEIGHTED_BITS",
    "SignedCarryBudgetExceeded",
    "WeightedCarryBlock",
    "WideSignedCarryAction",
]
