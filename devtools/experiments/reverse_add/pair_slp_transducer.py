"""Research-only exact pair-alphabet successor on run-length SLPs.

For every admitted decimal reverse/add occurrence the symmetric pair word has
alphabet ``0..18``.  Its residue modulo 32 therefore determines the exact pair
word.  This module applies the physical LSD-to-MSD carry transducer directly
to an RLSLP, emits the digit RLSLP, reflects it structurally, and constructs
the next pair word by an exact synchronized sum.

This closes *spatial* successor semantics.  It is not a temporal pump: the
synchronized zipper can create a new alignment state for each distinct pair
of grammar fragments.  The charged ``zip_splits`` counter exposes that cost.
No production code imports this module.
"""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from typing import TypeVar

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class PairStep:
    input_root: int
    digit_root: int
    pair_root: int
    growth: int
    created_nodes: int
    zip_splits: int


@dataclass(frozen=True, slots=True)
class UniformTwoSixStepClause:
    """Binary-encoded spatial clause ``2^m -> 661 2^(m-4) 166``.

    This is an executable candidate clause for ``m >= 4``.  It has an actual
    source family (the decimal repunit of width ``m``), but this module does
    not provide the missing universal temporal-pump induction.
    """

    width: int
    source_root: int
    target_root: int
    events: int = 6
    growth: int = 2


@dataclass(frozen=True, slots=True)
class _Effect:
    output_low: int
    output_high: int
    final_low: int
    final_high: int

    def output(self, carry: int) -> int:
        return self.output_high if carry else self.output_low

    def final(self, carry: int) -> int:
        return self.final_high if carry else self.final_low


_K = TypeVar("_K")
_V = TypeVar("_V")


def _node_units(node: SLPNode) -> int:
    bits = sum(
        max(1, abs(value).bit_length())
        for value in (
            node.id,
            node.length,
            node.symbol,
            node.left,
            node.right,
            node.child,
            node.count,
        )
    )
    return max(1, (bits + 63) // 64)


def _slp_children(node: SLPNode) -> tuple[int, ...]:
    if node.kind == "CONCAT":
        return node.left, node.right
    if node.kind == "REPEAT":
        return (node.child,)
    return ()


def _push_slp_children(
    stack: list[tuple[int, bool]], node_id: int, children: tuple[int, ...]
) -> None:
    stack.append((node_id, True))
    stack.extend((child, False) for child in reversed(children))


def _defer_slp_node(
    arena: SLPArena, stack: list[tuple[int, bool]], node_id: int, expanded: bool
) -> bool:
    if expanded:
        return False
    children = _slp_children(arena.nodes[node_id])
    if not children:
        return False
    _push_slp_children(stack, node_id, children)
    return True


class PairSLPTransducer:
    """Ledger-owned spatial successor grammar for exact pair-alphabet SLPs."""

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("pair SLP transduction requires a resource ledger")
        self.ledger = ledger
        prefix = f"reverse-pair-slp-{ledger.owner_count}"
        self._node_owner = ledger.register(prefix + "-nodes", "query_memo")
        self._memo_owner = ledger.register(prefix + "-memo", "query_memo")
        self._work_owner = ledger.register(prefix + "-work", "query_memo")
        ledger.reserve(self._node_owner, entries=1, nodes=1)
        try:
            self._arena = SLPArena()
        except BaseException:
            ledger.release(self._node_owner, entries=1, nodes=1)
            ledger.mark_disposed(self._node_owner)
            ledger.mark_disposed(self._memo_owner)
            ledger.mark_disposed(self._work_owner)
            raise
        ledger.register_container(
            self._node_owner,
            self._arena.nodes,
            node_count=lambda: sum(_node_units(node) for node in self._arena.nodes),
            payloads=lambda: self._arena.nodes,
        )
        self._effects: dict[int, _Effect] = {}
        self._reverse: dict[int, int] = {}
        self._slices: dict[tuple[int, int, int], int] = {}
        self._zips: dict[tuple[int, int], int] = {}
        self._scales: dict[tuple[int, int], int] = {}
        self._equals: dict[tuple[int, int], bool] = {}
        self._memo_entries = 0
        self._closed = False

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed pair SLP transducer")

    def _validate_root(self, root: int) -> SLPNode:
        if type(root) is not int or not 0 <= root < len(self._arena.nodes):
            raise ValueError("pair SLP root is foreign or out of range")
        node = self._arena.nodes[root]
        if type(node) is not SLPNode or node.id != root:
            raise ValueError("pair SLP root identity was altered")
        return node

    def _validate_graph(self, root: int) -> None:
        pending = [root]
        seen: set[int] = set()
        while pending:
            node_id = pending.pop()
            if node_id in seen:
                continue
            seen.add(node_id)
            self.ledger.bump("reverse_pair_slp_validation_nodes")
            node = self._validate_root(node_id)
            if node.kind == "EMPTY":
                valid = node_id == self._arena.empty_id and node == SLPNode(
                    node_id, "EMPTY", 0
                )
            elif node.kind == "TERM":
                valid = (
                    node.length == 1
                    and 0 <= node.symbol <= 18
                    and node.left == node.right == node.child == -1
                    and node.count == 0
                    and self._arena._term.get(node.symbol) == node_id
                )
            elif node.kind == "CONCAT":
                valid = (
                    0 <= node.left < node_id
                    and 0 <= node.right < node_id
                    and node.symbol == node.child == -1
                    and node.count == 0
                    and self._arena._cat.get((node.left, node.right)) == node_id
                    and node.length
                    == self._arena.nodes[node.left].length
                    + self._arena.nodes[node.right].length
                )
                pending.extend((node.left, node.right))
            elif node.kind == "REPEAT":
                valid = (
                    0 <= node.child < node_id
                    and node.count >= 2
                    and node.symbol == node.left == node.right == -1
                    and self._arena._rep.get((node.child, node.count)) == node_id
                    and node.length == self._arena.nodes[node.child].length * node.count
                )
                pending.append(node.child)
            else:
                valid = False
            if not valid:
                raise ValueError("pair SLP graph was altered or left its alphabet")

    def node(self, root: int) -> SLPNode:
        """Return immutable research metadata without exposing the mutable arena."""
        self._check_open()
        return self._validate_root(root)

    def reachable(self, root: int) -> frozenset[int]:
        self._check_open()
        self._validate_graph(root)
        seen: set[int] = set()
        pending = [root]
        while pending:
            node_id = pending.pop()
            if node_id in seen:
                continue
            seen.add(node_id)
            node = self._arena.nodes[node_id]
            if node.kind == "CONCAT":
                pending.extend((node.left, node.right))
            elif node.kind == "REPEAT":
                pending.append(node.child)
        return frozenset(seen)

    @property
    def node_count(self) -> int:
        self._check_open()
        return len(self._arena.nodes)

    @contextmanager
    def _work(self, counter: str) -> Iterator[None]:
        self.ledger.reserve(self._work_owner, entries=1, nodes=1)
        self.ledger.bump(counter)
        try:
            yield
        finally:
            self.ledger.release(self._work_owner, entries=1, nodes=1)

    def _remember(self, memo: dict[_K, _V], key: _K, value: _V) -> _V:
        if key not in memo:
            self.ledger.reserve(self._memo_owner, entries=1, nodes=1)
            memo[key] = value
            self._memo_entries += 1
        return memo[key]

    def _reserve_node(self, predicted: SLPNode) -> None:
        self.ledger.reserve(self._node_owner, entries=1, nodes=_node_units(predicted))

    def terminal(self, symbol: int) -> int:
        self._check_open()
        if type(symbol) is not int or not 0 <= symbol <= 18:
            raise ValueError("pair/digit grammar symbol must lie in 0..18")
        old = self._arena._term.get(symbol)
        if old is not None:
            return old
        predicted = SLPNode(len(self._arena.nodes), "TERM", 1, symbol=symbol)
        self._reserve_node(predicted)
        return self._arena.terminal(symbol)

    def concat(self, left: int, right: int) -> int:
        self._check_open()
        self._validate_root(left)
        self._validate_root(right)
        if left == self._arena.empty_id:
            return right
        if right == self._arena.empty_id:
            return left
        old = self._arena._cat.get((left, right))
        if old is not None:
            return old
        predicted = SLPNode(
            len(self._arena.nodes),
            "CONCAT",
            self._arena.nodes[left].length + self._arena.nodes[right].length,
            left=left,
            right=right,
        )
        self._reserve_node(predicted)
        return self._arena.concat(left, right)

    def concat_many(self, roots: tuple[int, ...]) -> int:
        self._check_open()
        for root in roots:
            self._validate_root(root)
        row = [root for root in roots if root != self._arena.empty_id]
        while len(row) > 1:
            row = [
                self.concat(row[index], row[index + 1])
                if index + 1 < len(row)
                else row[index]
                for index in range(0, len(row), 2)
            ]
        return row[0] if row else self._arena.empty_id

    def repeat(self, child: int, count: int) -> int:
        self._check_open()
        self._validate_root(child)
        if type(count) is not int or count < 0:
            raise ValueError("SLP repetition count must be nonnegative")
        if count == 0 or child == self._arena.empty_id:
            return self._arena.empty_id
        if count == 1:
            return child
        node = self._arena.nodes[child]
        while node.kind == "REPEAT":
            count *= node.count
            child = node.child
            node = self._arena.nodes[child]
        old = self._arena._rep.get((child, count))
        if old is not None:
            return old
        predicted = SLPNode(
            len(self._arena.nodes),
            "REPEAT",
            node.length * count,
            child=child,
            count=count,
        )
        self._reserve_node(predicted)
        return self._arena.repeat(child, count)

    def word(self, values: tuple[int, ...]) -> int:
        self._check_open()
        return self.concat_many(tuple(self.terminal(value) for value in values))

    def _compose(self, before: _Effect, after: _Effect) -> _Effect:
        outputs = []
        finals = []
        for carry in (0, 1):
            middle = before.final(carry)
            outputs.append(self.concat(before.output(carry), after.output(middle)))
            finals.append(after.final(middle))
        return _Effect(outputs[0], outputs[1], finals[0], finals[1])

    def _power(self, effect: _Effect, count: int) -> _Effect:
        if count and all(
            effect.final(effect.final(carry)) == effect.final(carry) for carry in (0, 1)
        ):
            outputs = []
            finals = []
            for carry in (0, 1):
                fixed = effect.final(carry)
                first = effect.output(carry)
                steady = effect.output(fixed)
                if first == steady:
                    outputs.append(self.repeat(first, count))
                else:
                    outputs.append(self.concat(first, self.repeat(steady, count - 1)))
                finals.append(fixed)
            self.ledger.bump("reverse_pair_slp_fixed_carry_pumps")
            return _Effect(outputs[0], outputs[1], finals[0], finals[1])
        identity = _Effect(self._arena.empty_id, self._arena.empty_id, 0, 1)
        result = identity
        power = effect
        while count:
            if count & 1:
                result = self._compose(result, power)
            count >>= 1
            if count:
                power = self._compose(power, power)
            self.ledger.bump("reverse_pair_slp_power_bits")
        return result

    def _effect(self, root: int) -> _Effect:
        stack = [(root, False)]
        while stack:
            node_id, expanded = stack.pop()
            if node_id in self._effects:
                continue
            if _defer_slp_node(self._arena, stack, node_id, expanded):
                continue
            node = self._arena.nodes[node_id]
            with self._work("reverse_pair_slp_effect_nodes"):
                if node.kind == "EMPTY":
                    result = _Effect(node_id, node_id, 0, 1)
                elif node.kind == "TERM":
                    low, high = node.symbol, node.symbol + 1
                    result = _Effect(
                        self.terminal(low % 10),
                        self.terminal(high % 10),
                        low // 10,
                        high // 10,
                    )
                elif node.kind == "CONCAT":
                    result = self._compose(
                        self._effects[node.left], self._effects[node.right]
                    )
                elif node.kind == "REPEAT":
                    result = self._power(self._effects[node.child], node.count)
                else:
                    raise ValueError("unknown SLP node kind")
            self._remember(self._effects, node_id, result)
        return self._effects[root]

    def reverse(self, root: int) -> int:
        self._check_open()
        self._validate_root(root)
        stack = [(root, False)]
        while stack:
            node_id, expanded = stack.pop()
            if node_id in self._reverse:
                continue
            if _defer_slp_node(self._arena, stack, node_id, expanded):
                continue
            node = self._arena.nodes[node_id]
            with self._work("reverse_pair_slp_reverse_nodes"):
                if node.kind in ("EMPTY", "TERM"):
                    result = node_id
                elif node.kind == "CONCAT":
                    result = self.concat(
                        self._reverse[node.right], self._reverse[node.left]
                    )
                elif node.kind == "REPEAT":
                    result = self.repeat(self._reverse[node.child], node.count)
                else:
                    raise ValueError("unknown SLP node kind")
            self._remember(self._reverse, node_id, result)
        return self._reverse[root]

    def slice(self, root: int, start: int, stop: int) -> int:
        self._check_open()
        self._validate_root(root)
        node = self._arena.nodes[root]
        if not 0 <= start <= stop <= node.length:
            raise ValueError("SLP slice lies outside its represented interval")
        if start == 0 and stop == node.length:
            return root
        if start == stop:
            return self._arena.empty_id
        key = root, start, stop
        found = self._slices.get(key)
        if found is not None:
            return found
        stack = [(key, False)]

        def resolved(item: tuple[int, int, int]) -> int:
            node_id, item_start, item_stop = item
            length = self._arena.nodes[node_id].length
            if item_start == item_stop:
                return self._arena.empty_id
            if item_start == 0 and item_stop == length:
                return node_id
            return self._slices[item]

        while stack:
            item, expanded = stack.pop()
            if item in self._slices:
                continue
            node_id, item_start, item_stop = item
            current = self._arena.nodes[node_id]
            dependencies: tuple[tuple[int, int, int], ...]
            full_count = 0
            if current.kind == "CONCAT":
                boundary = self._arena.nodes[current.left].length
                if item_stop <= boundary:
                    dependencies = ((current.left, item_start, item_stop),)
                elif boundary <= item_start:
                    dependencies = (
                        (
                            current.right,
                            item_start - boundary,
                            item_stop - boundary,
                        ),
                    )
                else:
                    dependencies = (
                        (current.left, item_start, boundary),
                        (current.right, 0, item_stop - boundary),
                    )
            elif current.kind == "REPEAT":
                child_length = self._arena.nodes[current.child].length
                start_copy = item_start // child_length
                stop_copy = (item_stop - 1) // child_length
                if start_copy == stop_copy:
                    dependencies = (
                        (
                            current.child,
                            item_start % child_length,
                            (item_stop - 1) % child_length + 1,
                        ),
                    )
                else:
                    dependencies_list = []
                    if item_start % child_length:
                        dependencies_list.append(
                            (current.child, item_start % child_length, child_length)
                        )
                    first_full = (item_start + child_length - 1) // child_length
                    stop_full = item_stop // child_length
                    full_count = max(0, stop_full - first_full)
                    if item_stop % child_length:
                        dependencies_list.append(
                            (current.child, 0, item_stop % child_length)
                        )
                    dependencies = tuple(dependencies_list)
            else:
                raise AssertionError("a proper nonempty terminal slice is impossible")
            missing = tuple(
                dependency
                for dependency in dependencies
                if dependency[1] != dependency[2]
                and not (
                    dependency[1] == 0
                    and dependency[2] == self._arena.nodes[dependency[0]].length
                )
                and dependency not in self._slices
            )
            if missing and not expanded:
                stack.append((item, True))
                stack.extend((dependency, False) for dependency in reversed(missing))
                continue
            with self._work("reverse_pair_slp_slice_splits"):
                parts = [resolved(dependency) for dependency in dependencies]
                if current.kind == "REPEAT" and full_count:
                    insertion = (
                        1 if item_start % self._arena.nodes[current.child].length else 0
                    )
                    parts.insert(insertion, self.repeat(current.child, full_count))
                result = self.concat_many(tuple(parts))
            self._remember(self._slices, item, result)
        return self._slices[key]

    def scale(self, root: int, coefficient: int) -> int:
        self._check_open()
        self._validate_root(root)
        stack = [(root, False)]
        while stack:
            node_id, expanded = stack.pop()
            key = node_id, coefficient
            if key in self._scales:
                continue
            if _defer_slp_node(self._arena, stack, node_id, expanded):
                continue
            node = self._arena.nodes[node_id]
            with self._work("reverse_pair_slp_scale_nodes"):
                if node.kind == "EMPTY":
                    result = node_id
                elif node.kind == "TERM":
                    result = self.terminal(coefficient * node.symbol)
                elif node.kind == "CONCAT":
                    result = self.concat(
                        self._scales[(node.left, coefficient)],
                        self._scales[(node.right, coefficient)],
                    )
                elif node.kind == "REPEAT":
                    result = self.repeat(
                        self._scales[(node.child, coefficient)], node.count
                    )
                else:
                    raise ValueError("unknown SLP node kind")
            self._remember(self._scales, key, result)
        return self._scales[(root, coefficient)]

    @staticmethod
    def _first_span(node: SLPNode, arena: SLPArena) -> int:
        if node.kind == "CONCAT":
            return arena.nodes[node.left].length
        # Treat a repeated block as one maximal span.  Its slice operation can
        # split the repetition arithmetically; peeling one child here would
        # turn a one-cell repeated core into represented-position recursion.
        if node.kind == "REPEAT":
            return node.length
        return node.length

    @staticmethod
    def _zip_key(left: int, right: int) -> tuple[int, int]:
        """Canonicalize the exact commutative pair-sum request."""
        return (left, right) if left <= right else (right, left)

    def zip_sum(self, left: int, right: int) -> int:
        """Pointwise sum whose output must remain in the pair alphabet 0..18.

        The successor supplies normalized digit operands (0..9); arbitrary
        pair-field inputs need not admit another pair-field sum.
        """
        self._check_open()
        self._validate_root(left)
        self._validate_root(right)
        if self._arena.nodes[left].length != self._arena.nodes[right].length:
            raise ValueError("synchronized SLP sum requires equal extents")
        key = self._zip_key(left, right)
        found = self._zips.get(key)
        if found is not None:
            return found
        stack = [(key, False)]
        while stack:
            item, expanded = stack.pop()
            if item in self._zips:
                continue
            item_left, item_right = item
            left_node = self._arena.nodes[item_left]
            right_node = self._arena.nodes[item_right]
            mode: str
            dependencies: tuple[tuple[int, int], ...] = ()
            repeat_count = 0
            repeat_dependency: tuple[int, int] | None = None
            concat_dependencies: tuple[tuple[int, int], tuple[int, int]] | None = None
            if item_left == item_right:
                mode = "scale"
            elif left_node.kind == right_node.kind == "TERM":
                mode = "term"
            elif (
                left_node.kind == right_node.kind == "REPEAT"
                and left_node.count == right_node.count
                and self._arena.nodes[left_node.child].length
                == self._arena.nodes[right_node.child].length
            ):
                mode = "repeat"
                repeat_count = left_node.count
                repeat_dependency = self._zip_key(left_node.child, right_node.child)
                dependencies = (repeat_dependency,)
            elif (
                left_node.kind == right_node.kind == "CONCAT"
                and self._arena.nodes[left_node.left].length
                == self._arena.nodes[right_node.left].length
            ):
                mode = "concat"
                concat_dependencies = (
                    self._zip_key(left_node.left, right_node.left),
                    self._zip_key(left_node.right, right_node.right),
                )
                dependencies = concat_dependencies
            else:
                mode = "concat"
                split = min(
                    self._first_span(left_node, self._arena),
                    self._first_span(right_node, self._arena),
                )
                length = left_node.length
                if not 0 < split < length:
                    raise ValueError("synchronized SLP alignment did not refine")
                self.ledger.bump("reverse_pair_slp_zip_splits")
                concat_dependencies = (
                    self._zip_key(
                        self.slice(item_left, 0, split),
                        self.slice(item_right, 0, split),
                    ),
                    self._zip_key(
                        self.slice(item_left, split, length),
                        self.slice(item_right, split, length),
                    ),
                )
                dependencies = concat_dependencies
            missing = tuple(dep for dep in dependencies if dep not in self._zips)
            if missing and not expanded:
                stack.append((item, True))
                stack.extend((dep, False) for dep in reversed(missing))
                continue
            with self._work("reverse_pair_slp_zip_states"):
                if mode == "scale":
                    result = self.scale(item_left, 2)
                elif mode == "term":
                    result = self.terminal(left_node.symbol + right_node.symbol)
                elif mode == "repeat":
                    if repeat_dependency is None:
                        raise AssertionError("repeat zip lost its child dependency")
                    result = self.repeat(self._zips[repeat_dependency], repeat_count)
                else:
                    if concat_dependencies is None:
                        raise AssertionError("concat zip lost its child dependencies")
                    result = self.concat(
                        self._zips[concat_dependencies[0]],
                        self._zips[concat_dependencies[1]],
                    )
            self._remember(self._zips, item, result)
        return self._zips[key]

    def exact_equal(self, left: int, right: int) -> bool:
        """Decide equality by structural alignment, without word expansion."""
        self._check_open()
        self._validate_graph(left)
        self._validate_graph(right)
        left_node, right_node = self._validate_root(left), self._validate_root(right)
        if left_node.length != right_node.length:
            return False
        if left == right:
            return True
        key = left, right
        if key in self._equals:
            return self._equals[key]
        stack = [(key, False)]
        while stack:
            item, expanded = stack.pop()
            if item in self._equals:
                continue
            item_left, item_right = item
            if item_left == item_right:
                self._remember(self._equals, item, True)
                continue
            left_node, right_node = (
                self._arena.nodes[item_left],
                self._arena.nodes[item_right],
            )
            if left_node.length != right_node.length:
                self._remember(self._equals, item, False)
                continue
            dependencies: tuple[tuple[int, int], ...] = ()
            if left_node.kind == right_node.kind == "TERM":
                direct: bool | None = left_node.symbol == right_node.symbol
            elif (
                left_node.kind == right_node.kind == "REPEAT"
                and left_node.count == right_node.count
                and self._arena.nodes[left_node.child].length
                == self._arena.nodes[right_node.child].length
            ):
                direct = None
                dependencies = ((left_node.child, right_node.child),)
            elif (
                left_node.kind == right_node.kind == "CONCAT"
                and self._arena.nodes[left_node.left].length
                == self._arena.nodes[right_node.left].length
            ):
                direct = None
                dependencies = (
                    (left_node.left, right_node.left),
                    (left_node.right, right_node.right),
                )
            else:
                direct = None
                split = min(
                    self._first_span(left_node, self._arena),
                    self._first_span(right_node, self._arena),
                )
                if split == left_node.length:
                    spans = [
                        self._arena.nodes[node.child].length
                        for node in (left_node, right_node)
                        if node.kind == "REPEAT"
                    ]
                    split = min(spans, default=split)
                if not 0 < split < left_node.length:
                    direct = False
                else:
                    dependencies = (
                        (
                            self.slice(item_left, 0, split),
                            self.slice(item_right, 0, split),
                        ),
                        (
                            self.slice(item_left, split, left_node.length),
                            self.slice(item_right, split, right_node.length),
                        ),
                    )
            if direct is not None:
                self._remember(self._equals, item, direct)
                continue
            missing = tuple(dep for dep in dependencies if dep not in self._equals)
            if missing and not expanded:
                stack.append((item, True))
                stack.extend((dep, False) for dep in reversed(missing))
                continue
            with self._work("reverse_pair_slp_equality_states"):
                result = all(self._equals[dep] for dep in dependencies)
            self._remember(self._equals, item, result)
        return self._equals[key]

    def pair_from_digits(self, digits: int) -> int:
        self._check_open()
        self._validate_graph(digits)
        return self.zip_sum(digits, self.reverse(digits))

    def uniform_two_six_step_clause(self, width: int) -> UniformTwoSixStepClause:
        """Build the derived six-event parameter clause without unrolling width."""
        self._check_open()
        if type(width) is not int or width < 4:
            raise ValueError("uniform-two clause requires width at least four")
        two = self.terminal(2)
        source = self.repeat(two, width)
        target = self.concat_many(
            (
                self.word((6, 6, 1)),
                self.repeat(two, width - 4),
                self.word((1, 6, 6)),
            )
        )
        return UniformTwoSixStepClause(width, source, target)

    def successor(self, pair: int) -> PairStep:
        self._check_open()
        self._validate_graph(pair)
        before_nodes = len(self._arena.nodes)
        before_splits = self.ledger.counters.get("reverse_pair_slp_zip_splits", 0)
        effect = self._effect(pair)
        growth = effect.final_low
        digits = effect.output_low
        if growth:
            digits = self.concat(digits, self.terminal(growth))
        following = self.pair_from_digits(digits)
        return PairStep(
            pair,
            digits,
            following,
            growth,
            len(self._arena.nodes) - before_nodes,
            self.ledger.counters.get("reverse_pair_slp_zip_splits", 0) - before_splits,
        )

    def close(self) -> None:
        if self._closed:
            return
        self._effects.clear()
        self._reverse.clear()
        self._slices.clear()
        self._zips.clear()
        self._scales.clear()
        self._equals.clear()
        if self._memo_entries:
            self.ledger.release(
                self._memo_owner,
                entries=self._memo_entries,
                nodes=self._memo_entries,
            )
        count = len(self._arena.nodes)
        units = sum(_node_units(node) for node in self._arena.nodes)
        self._arena.nodes.clear()
        self._arena._term.clear()
        self._arena._cat.clear()
        self._arena._rep.clear()
        self.ledger.release(self._node_owner, entries=count, nodes=units)
        self.ledger.mark_disposed(self._node_owner)
        self.ledger.mark_disposed(self._memo_owner)
        self.ledger.mark_disposed(self._work_owner)
        self._closed = True


__all__ = ["PairSLPTransducer", "PairStep", "UniformTwoSixStepClause"]
