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

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance

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


def _weighted_summary_for_node(
    arena: SLPArena,
    node_id: int,
    summaries: Mapping[int, WeightedCarryBlock],
    *,
    max_width: int,
    max_weighted_bits: int,
) -> WeightedCarryBlock:
    """Recompute one source-node action from already checked child summaries."""
    node = arena.nodes[node_id]
    if node.kind == "EMPTY":
        summary = WeightedCarryBlock(0, 0)
    elif node.kind == "TERM":
        if node.symbol.bit_length() > max_weighted_bits:
            raise SignedCarryBudgetExceeded(
                "source coefficient exceeds weighted integer budget"
            )
        summary = WeightedCarryBlock(1, node.symbol)
    elif node.kind == "CONCAT":
        if node.left >= node_id or node.right >= node_id:
            raise ArithmeticError("signed carry SLP child is not topologically earlier")
        left = summaries.get(node.left)
        right = summaries.get(node.right)
        if (
            type(left) is not WeightedCarryBlock
            or type(right) is not WeightedCarryBlock
        ):
            raise ArithmeticError("signed carry source child summary is missing")
        summary = left.then(
            right,
            max_length=max_width,
            max_weighted_bits=max_weighted_bits,
        )
    elif node.kind == "REPEAT":
        if node.child >= node_id:
            raise ArithmeticError("signed carry SLP child is not topologically earlier")
        child = summaries.get(node.child)
        if type(child) is not WeightedCarryBlock:
            raise ArithmeticError("signed carry repeat child summary is missing")
        summary = child.power(
            node.count,
            max_length=max_width,
            max_weighted_bits=max_weighted_bits,
        )
    else:  # pragma: no cover - arena invariant
        raise AssertionError(node.kind)
    if summary.length != node.length:
        raise ArithmeticError("signed carry node summary length mismatch")
    return summary


def _signed_seam_fields(
    block: WeightedCarryBlock, width: int, sign: int
) -> tuple[int, bool, int]:
    """Derive the canonical residue, signed exception, and initial carry."""
    modulus = (1 << width) - sign
    residue = block.value % modulus
    signed_minus_one = sign == -1 and residue == (1 << width)
    if signed_minus_one:
        c0 = -((block.value + 1) // modulus)
    elif sign == -1:
        c0 = -(block.value // modulus)
    else:
        # Cyclic residue zero has a second all-ones representation; the
        # canonical emitted word is all zeroes.
        c0 = block.value // modulus
    return residue, signed_minus_one, c0


@dataclass(frozen=True, slots=True)
class _CarryLeaf:
    block: WeightedCarryBlock
    symbols: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _CarryJoin:
    block: WeightedCarryBlock
    left: int
    right: int


@dataclass(frozen=True, slots=True)
class _CarryRepeat:
    block: WeightedCarryBlock
    child: int
    count: int


_CarryRow = _CarryLeaf | _CarryJoin | _CarryRepeat
_CARRY_CHUNK_LENGTH = 64


@dataclass(frozen=True, slots=True)
class _CarryPlan:
    """Request-local evaluation rows, never semantic or source-authority IDs."""

    rows: tuple[_CarryRow, ...]
    root: int

    def prefix(self, count: int, *, width: int, bits: int) -> WeightedCarryBlock:
        result = WeightedCarryBlock(0, 0)
        index = self.root
        while count:
            row = self.rows[index]
            if count == row.block.length:
                return result.then(row.block, max_length=width, max_weighted_bits=bits)
            if isinstance(row, _CarryJoin):
                left = self.rows[row.left].block
                if count <= left.length:
                    index = row.left
                else:
                    result = result.then(left, max_length=width, max_weighted_bits=bits)
                    count -= left.length
                    index = row.right
            elif isinstance(row, _CarryRepeat):
                child = self.rows[row.child].block
                copies, count = divmod(count, child.length)
                repeated = child.power(copies, max_length=width, max_weighted_bits=bits)
                result = result.then(repeated, max_length=width, max_weighted_bits=bits)
                index = row.child
            else:
                for coefficient in row.symbols[:count]:
                    result = result.then(
                        WeightedCarryBlock(1, coefficient),
                        max_length=width,
                        max_weighted_bits=bits,
                    )
                return result
        return result

    def coefficient(self, position: int) -> int:
        index = self.root
        while True:
            row = self.rows[index]
            if isinstance(row, _CarryLeaf):
                return row.symbols[position]
            if isinstance(row, _CarryRepeat):
                position %= self.rows[row.child].block.length
                index = row.child
            else:
                left_length = self.rows[row.left].block.length
                if position < left_length:
                    index = row.left
                else:
                    position -= left_length
                    index = row.right

    def exact_match(self, other: _CarryPlan) -> bool:
        """Compare every demanded row, including prefix-only data and exact types."""
        if type(self.rows) is not tuple or type(self.root) is not int:
            return False
        if self.root != other.root or len(self.rows) != len(other.rows):
            return False
        for actual, expected in zip(self.rows, other.rows, strict=True):
            if (
                type(actual) is not type(expected)
                or type(actual.block) is not WeightedCarryBlock
            ):
                return False
            actual.block.__post_init__()
            if isinstance(actual, _CarryLeaf):
                if type(actual.symbols) is not tuple or any(
                    type(x) is not int for x in actual.symbols
                ):
                    return False
            elif isinstance(actual, _CarryJoin):
                if type(actual.left) is not int or type(actual.right) is not int:
                    return False
            elif type(actual.child) is not int or type(actual.count) is not int:
                return False
            if actual != expected:
                return False
        return True


def _needs_carry_plan(arena: SLPArena, reachable: list[int], width: int) -> bool:
    # A selection based on structural footprint, not a physical occurrence ID.
    footprint = sum(arena.nodes[i].length for i in reachable)
    if footprint <= 128_000:
        return False
    depths: dict[int, int] = {}
    for index in reachable:
        node = arena.nodes[index]
        depth = (
            1 + max(depths.get(node.left, 0), depths.get(node.right, 0))
            if node.kind == "CONCAT"
            else 0
        )
        depths[index] = depth
        # Repetition does not hide an expensive CONCAT region inside its child.
        if depth > 128:
            return True
    return footprint > 32 * width


def _build_carry_plan(
    arena: SLPArena, root: int, reachable: list[int], *, width: int, bits: int
) -> _CarryPlan:
    """Rebalance CONCAT arithmetic; retain each REPEAT as a powered row.

    Only repeat-child regions need separate plans. Topological source order
    makes their construction iterative even for deeply nested source grammars.
    No coefficient history or growing prefix integer is retained.
    """
    rows: list[_CarryRow] = []
    compiled: dict[int, int] = {}
    regions = {root}
    for index in reachable:
        node = arena.nodes[index]
        if node.kind == "CONCAT":
            if not (0 <= node.left < index and 0 <= node.right < index):
                raise ArithmeticError("carry source is not topological")
            expected = arena.nodes[node.left].length + arena.nodes[node.right].length
        elif node.kind == "REPEAT":
            if (
                not 0 <= node.child < index
                or type(node.count) is not int
                or node.count < 1
            ):
                raise ArithmeticError("invalid carry repeat")
            expected = arena.nodes[node.child].length * node.count
            regions.add(node.child)
        elif node.kind == "TERM":
            if type(node.symbol) is not int or node.symbol.bit_length() > bits:
                raise SignedCarryBudgetExceeded(
                    "source coefficient exceeds weighted integer budget"
                )
            expected = 1
        elif node.kind == "EMPTY":
            expected = 0
        else:
            raise ArithmeticError("unknown carry source node")
        if type(node.length) is not int or node.length != expected:
            raise ArithmeticError("carry source length mismatch")

    def append(row: _CarryRow) -> int:
        rows.append(row)
        return len(rows) - 1

    def join(left: int, right: int) -> int:
        block = rows[left].block.then(
            rows[right].block, max_length=width, max_weighted_bits=bits
        )
        return append(_CarryJoin(block, left, right))

    def publish(index: int, frontier: list[tuple[int, int]]) -> None:
        level = 0
        while frontier and frontier[-1][0] == level:
            index = join(frontier.pop()[1], index)
            level += 1
        frontier.append((level, index))

    def flush(chunk: list[int], frontier: list[tuple[int, int]]) -> None:
        if not chunk:
            return
        block = WeightedCarryBlock(0, 0)
        for coefficient in chunk:
            block = block.then(
                WeightedCarryBlock(1, coefficient),
                max_length=width,
                max_weighted_bits=bits,
            )
        publish(append(_CarryLeaf(block, tuple(chunk))), frontier)
        chunk.clear()

    for region in sorted(regions):
        if region in compiled:
            continue
        tasks = [region]
        chunk: list[int] = []
        frontier: list[tuple[int, int]] = []
        while tasks:
            index = tasks.pop()
            if index in compiled:
                flush(chunk, frontier)
                publish(compiled[index], frontier)
                continue
            node = arena.nodes[index]
            if node.kind == "CONCAT":
                tasks.extend((node.right, node.left))
            elif node.kind == "TERM":
                chunk.append(node.symbol)
                if len(chunk) == _CARRY_CHUNK_LENGTH:
                    flush(chunk, frontier)
            elif node.kind == "REPEAT":
                flush(chunk, frontier)
                child = compiled[node.child]
                block = rows[child].block.power(
                    node.count, max_length=width, max_weighted_bits=bits
                )
                compiled[index] = append(_CarryRepeat(block, child, node.count))
                publish(compiled[index], frontier)
        flush(chunk, frontier)
        if not frontier:
            output = append(_CarryLeaf(WeightedCarryBlock(0, 0), ()))
        else:
            output = frontier[0][1]
            for _, index in frontier[1:]:
                output = join(output, index)
        if rows[output].block.length != arena.nodes[region].length:
            raise ArithmeticError("balanced carry region length mismatch")
        compiled[region] = output
    return _CarryPlan(tuple(rows), compiled[root])


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
        if not is_runtime_instance(arena, SLPArena):
            raise TypeError("a signed carry source must be an SLP arena")
        if arena.node_storage_poisoned:
            raise RuntimeError(
                "signed carry cannot admit an SLP arena with stale interners"
            )
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
        self._source_arena = arena
        self._source_node_storage = arena.nodes
        self._source_root = root
        self._source_node_id_generation = arena.node_id_generation
        self._source_sign = sign
        self._source_max_width = width_budget
        self._source_max_weighted_bits = bits_budget
        self.width = width
        self.sign = sign
        self.max_width = width_budget
        self.max_weighted_bits = bits_budget
        reachable = sorted(arena.reachable(root))
        self._plan: _CarryPlan | None = None
        self._summaries: dict[int, WeightedCarryBlock] = {}
        if _needs_carry_plan(arena, reachable, width):
            self._plan = _build_carry_plan(
                arena, root, reachable, width=width_budget, bits=bits_budget
            )
            self.block = self._plan.rows[self._plan.root].block
            self._summaries[root] = self.block
        else:
            for node_id in reachable:
                self._summaries[node_id] = _weighted_summary_for_node(
                    arena,
                    node_id,
                    self._summaries,
                    max_width=width_budget,
                    max_weighted_bits=bits_budget,
                )
            self.block = self._summaries[root]
        if self.block.length != width:
            raise ArithmeticError("SLP summary length mismatch")
        self.residue, self.signed_minus_one, self.c0 = _signed_seam_fields(
            self.block, width, sign
        )
        if self.carry_at(width) != sign * self.c0:
            raise ArithmeticError("cyclic/negacyclic signed seam did not close")

    def _check_source_binding(self) -> None:
        if (
            self.arena is not self._source_arena
            or self.arena.nodes is not self._source_node_storage
            or self.root != self._source_root
        ):
            raise RuntimeError("signed carry source arena or root changed")
        self.arena.empty()
        if self.arena.node_id_generation != self._source_node_id_generation:
            raise RuntimeError("signed carry source node IDs changed")

    def _prefix(self, count: int) -> WeightedCarryBlock:
        self._check_source_binding()
        if type(count) is not int or not 0 <= count <= self.width:
            raise IndexError(count)
        if self._plan is not None:
            return self._plan.prefix(
                count, width=self.max_width, bits=self.max_weighted_bits
            )
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
        self._check_source_binding()
        if type(position) is not int or not 0 <= position < self.width:
            raise IndexError(position)
        coefficient = self._coefficient_at(position)
        return self._digit_from_carry(position, coefficient, self.carry_at(position))

    def _coefficient_at(self, position: int) -> int:
        if self._plan is not None:
            return self._plan.coefficient(position)
        return symbol_at(self.arena, self.root, position)

    @property
    def retained_weighted_bits(self) -> int:
        """Logical weighted payload, excluding duplicated references to a block."""
        self._check_source_binding()
        if self._plan is not None:
            return sum(row.block.value.bit_length() for row in self._plan.rows)
        return sum(block.value.bit_length() for block in self._summaries.values())

    def _digit_from_carry(
        self, position: int, coefficient: int, incoming_carry: int
    ) -> int:
        if self.signed_minus_one and position == 0:
            return -1
        return (coefficient + incoming_carry) & 1

    def verify_cochain(self) -> bool:
        """Revalidate the coefficient DAG and its exact weighted carry seam.

        Binary division determines each local emitted digit. Telescoping those
        equations gives ``B + c0 = emission + 2**width * outgoing``; the
        canonical remainder (or the signed -1 exception) determines the whole
        emission. No expanded coefficient word is needed for this audit.
        """
        self._check_source_binding()
        root_summary: WeightedCarryBlock | None = None
        try:
            if (
                type(self.sign) is not int
                or self.sign not in (-1, 1)
                or self.sign != self._source_sign
                or type(self.width) is not int
                or self.width != self.arena.nodes[self.root].length
                or self.max_width != self._source_max_width
                or self.max_weighted_bits != self._source_max_weighted_bits
            ):
                return False
            width_budget = _budget(
                self.max_width, "carry-width-budget", MAX_SIGNED_CARRY_WIDTH
            )
            bits_budget = _budget(
                self.max_weighted_bits,
                "weighted-integer-budget",
                MAX_SIGNED_WEIGHTED_BITS,
                minimum=8,
            )
            if self.width > width_budget or type(self._summaries) is not dict:
                return False
            if any(type(node_id) is not int for node_id in self._summaries):
                return False
            reachable = sorted(self.arena.reachable(self.root))
            if _needs_carry_plan(self.arena, reachable, self.width):
                if type(self._plan) is not _CarryPlan or set(self._summaries) != {
                    self.root
                }:
                    return False
                checked = _build_carry_plan(
                    self.arena,
                    self.root,
                    reachable,
                    width=width_budget,
                    bits=bits_budget,
                )
                if not self._plan.exact_match(checked):
                    return False
                if self._summaries[self.root] != checked.rows[checked.root].block:
                    return False
            else:
                if self._plan is not None:
                    return False
                if len(self._summaries) != len(reachable):
                    return False
                for node_id in reachable:
                    stored = self._summaries.get(node_id)
                    if type(stored) is not WeightedCarryBlock:
                        return False
                    stored.__post_init__()
                    expected = _weighted_summary_for_node(
                        self.arena,
                        node_id,
                        self._summaries,
                        max_width=width_budget,
                        max_weighted_bits=bits_budget,
                    )
                    if stored != expected:
                        return False
            root_summary = self._summaries.get(self.root)
            if (
                type(root_summary) is not WeightedCarryBlock
                or type(self.block) is not WeightedCarryBlock
            ):
                return False
            self.block.__post_init__()
            if self.block != root_summary:
                return False
            expected_residue, expected_signed_minus_one, expected_c0 = (
                _signed_seam_fields(root_summary, self.width, self.sign)
            )
            if (
                type(self.residue) is not int
                or self.residue != expected_residue
                or type(self.signed_minus_one) is not bool
                or self.signed_minus_one is not expected_signed_minus_one
                or type(self.c0) is not int
                or self.c0 != expected_c0
            ):
                return False
        except (ArithmeticError, IndexError, KeyError, TypeError, ValueError):
            return False
        if type(root_summary) is not WeightedCarryBlock:
            return False

        # Recompute every reachable summary above on every audit. Only the
        # redundant word expansion is eliminated, not source or row checking.
        emission = -1 if self.signed_minus_one else self.residue
        outgoing = self.sign * self.c0
        return (
            root_summary.value + self.c0 == emission + (outgoing << self.width)
            and root_summary.apply(self.c0 + int(self.signed_minus_one)) == outgoing
        )

    def demand(self, positions: tuple[int, ...]) -> tuple[tuple[int, int, int], ...]:
        """Return ``(position, output digit, incoming carry)`` at requested cells."""
        self._check_source_binding()
        if type(positions) is not tuple:
            raise ValueError("positions must be an immutable tuple")
        if len(positions) > self.width:
            raise ValueError("position demand exceeds action width")
        if any(type(i) is not int or not 0 <= i < self.width for i in positions):
            raise IndexError(positions)
        if len(set(positions)) != len(positions):
            raise ValueError("positions must be unique")
        results: list[tuple[int, int, int]] = []
        for position in positions:
            carry = self.carry_at(position)
            coefficient = self._coefficient_at(position)
            digit = self._digit_from_carry(position, coefficient, carry)
            results.append((position, digit, carry))
        return tuple(results)


__all__ = [
    "MAX_SIGNED_CARRY_WIDTH",
    "MAX_SIGNED_WEIGHTED_BITS",
    "SignedCarryBudgetExceeded",
    "WeightedCarryBlock",
    "WideSignedCarryAction",
]
