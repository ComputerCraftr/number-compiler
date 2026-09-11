"""Exact, separately canonical domain/F5/Boolean spatial grammars.

The existing canonical-word owner supplies all rope construction and equality.
Gates walk aligned grammar intervals, never a represented run's positions.
These are explicit execution coordinates, not admitted public point-cache keys.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from itertools import product
from weakref import WeakValueDictionary

from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)

KINDS = {"domain": 3, "f5": 5, "bool": 2}


@dataclass(frozen=True, slots=True, weakref_slot=True)
class PlaneID:
    owner: object
    kind: str
    index: int
    root: words.CanonicalWord = field(compare=False, repr=False)


@dataclass(frozen=True, slots=True)
class PlaneGate:
    name: str
    inputs: tuple[str, ...]
    output: str
    table: tuple[int | None, ...]

    def __post_init__(self) -> None:
        if (
            type(self.name) is not str
            or type(self.inputs) is not tuple
            or not 1 <= len(self.inputs) <= 4
            or self.output not in KINDS
            or any(kind not in KINDS for kind in self.inputs)
            or type(self.table) is not tuple
        ):
            raise ValueError("invalid bounded plane gate signature")
        size = 1
        for kind in self.inputs:
            size *= KINDS[kind]
        if len(self.table) != size or any(
            value is not None
            and (type(value) is not int or not 0 <= value < KINDS[self.output])
            for value in self.table
        ):
            raise ValueError("invalid bounded plane gate table")

    @classmethod
    def build(
        cls,
        name: str,
        inputs: tuple[str, ...],
        output: str,
        law: Callable[..., int | None],
    ) -> PlaneGate:
        table = tuple(
            law(*values) for values in product(*(range(KINDS[k]) for k in inputs))
        )
        if any(
            value is not None
            and (type(value) is not int or not 0 <= value < KINDS[output])
            for value in table
        ):
            raise ValueError("plane gate output is outside its alphabet")
        return cls(name, inputs, output, table)

    def evaluate(self, values: tuple[int, ...]) -> int:
        index = 0
        for kind, value in zip(self.inputs, values, strict=True):
            if type(value) is not int or not 0 <= value < KINDS[kind]:
                raise ValueError("plane gate input is outside its alphabet")
            index = index * KINDS[kind] + value
        result = self.table[index]
        if result is None:
            raise ValueError("plane gate is undefined on this input")
        return result


_View = tuple[words.CanonicalWord, int]
_GateKey = tuple[PlaneGate, tuple[tuple[int, int], ...], int]


class PlaneAlgebra:
    """Transient gate workspace over independently shared canonical ropes.

    Issued handles retain their roots; the registry is weak. Clearing work
    releases temporary gate results, not externally retained carrier planes.
    Work limits apply before each new traversal task, including cache misses.
    This explicit endpoint library has no production resource-audit admission.
    """

    def __init__(self, *, max_work: int = 1_000_000) -> None:
        require_endpoint_construction()
        if type(max_work) is not int or max_work <= 0:
            raise ValueError("plane work budget must be positive")
        self.owner = object()
        self.max_work = max_work
        self.work = 0
        self._issued: WeakValueDictionary[tuple[str, int], PlaneID] = (
            WeakValueDictionary()
        )
        self._gates: dict[_GateKey, words.CanonicalWord] = {}

    def clear_work(self) -> None:
        self._gates.clear()
        self.work = 0

    def _tick(self) -> None:
        if self.work >= self.max_work:
            raise BlockContextBudgetExceeded("factored plane traversal budget exceeded")
        self.work += 1

    def _issue(self, kind: str, root: words.CanonicalWord) -> PlaneID:
        key = kind, root.node_id
        found = self._issued.get(key)
        if found is None:
            found = PlaneID(self.owner, kind, root.node_id, root)
            self._issued[key] = found
        return found

    def resolve(self, plane: PlaneID, kind: str | None = None) -> words.CanonicalWord:
        if (
            type(plane) is not PlaneID
            or plane.owner is not self.owner
            or plane.kind not in KINDS
            or kind is not None
            and plane.kind != kind
            or self._issued.get((plane.kind, plane.index)) is not plane
            or plane.index != plane.root.node_id
        ):
            raise ValueError("foreign, stale, or incorrectly sorted plane")
        words._validate_word(plane.root)
        return plane.root

    def constant(self, kind: str, value: int, width: int) -> PlaneID:
        require_endpoint_construction()
        if (
            kind not in KINDS
            or type(value) is not int
            or not 0 <= value < KINDS[kind]
            or type(width) is not int
            or width <= 0
        ):
            raise ValueError(
                "plane constant requires a bounded atom and positive width"
            )
        return self._issue(kind, words.run(value, width))

    def from_values(self, kind: str, values: tuple[int, ...]) -> PlaneID:
        require_endpoint_construction()
        if kind not in KINDS or type(values) is not tuple or not values:
            raise ValueError("plane source requires an immutable nonempty tuple")
        if any(type(v) is not int or not 0 <= v < KINDS[kind] for v in values):
            raise ValueError("plane source has another alphabet")
        return self._issue(kind, words.from_values(values))

    @staticmethod
    def _view(root: words.CanonicalWord, start: int, width: int) -> _View:
        while root.symbol is None:
            left, right = root.left, root.right
            if left is None or right is None:
                raise ValueError("nonempty plane lost its children")
            if start + width <= left.length:
                root = left
            elif start >= left.length:
                start -= left.length
                root = right
            else:
                break
        return root, start

    def _apply_views(
        self, gate: PlaneGate, views: tuple[_View, ...], width: int
    ) -> words.CanonicalWord:
        pending = [(views, width, False)]
        results: list[words.CanonicalWord] = []
        while pending:
            current, length, ready = pending.pop()
            current = tuple(self._view(root, start, length) for root, start in current)
            key = gate, tuple((root.node_id, start) for root, start in current), length
            found = self._gates.get(key)
            if found is not None:
                results.append(found)
                continue
            self._tick()
            if ready:
                right, left = results.pop(), results.pop()
                result = words.concat(left, right)
            elif all(root.symbol is not None for root, _ in current):
                values = tuple(
                    int(root.symbol) for root, _ in current if root.symbol is not None
                )
                result = words.run(gate.evaluate(values), length)
            else:
                split = min(
                    root.left.length - start
                    for root, start in current
                    if root.left is not None
                )
                pending.append((current, length, True))
                pending.append(
                    (
                        tuple((root, start + split) for root, start in current),
                        length - split,
                        False,
                    )
                )
                pending.append((current, split, False))
                continue
            self._gates[key] = result
            results.append(result)
        if len(results) != 1:
            raise AssertionError("plane gate lost its result stack")
        return results[0]

    def apply(self, gate: PlaneGate, *planes: PlaneID) -> PlaneID:
        require_endpoint_construction()
        if len(planes) != len(gate.inputs) or not planes:
            raise ValueError("plane gate has another arity")
        roots = tuple(
            self.resolve(p, k) for p, k in zip(planes, gate.inputs, strict=True)
        )
        width = roots[0].length
        if any(root.length != width for root in roots):
            raise ValueError("plane gate requires aligned widths")
        return self._issue(
            gate.output, self._apply_views(gate, tuple((r, 0) for r in roots), width)
        )

    def slice(self, plane: PlaneID, start: int, width: int) -> PlaneID:
        require_endpoint_construction()
        root = self.resolve(plane)
        if (
            type(start) is not int
            or type(width) is not int
            or start < 0
            or width <= 0
            or start + width > root.length
        ):
            raise ValueError("plane slice lies outside its field")
        gate = PlaneGate(
            "identity", (plane.kind,), plane.kind, tuple(range(KINDS[plane.kind]))
        )
        return self._issue(plane.kind, self._apply_views(gate, ((root, start),), width))

    def concat(self, left: PlaneID, right: PlaneID) -> PlaneID:
        require_endpoint_construction()
        a, b = self.resolve(left), self.resolve(right, left.kind)
        self._tick()
        return self._issue(left.kind, words.concat(a, b))

    def reverse(self, plane: PlaneID) -> PlaneID:
        require_endpoint_construction()
        self._tick()
        return self._issue(plane.kind, words.reverse(self.resolve(plane)))

    def shift(self, plane: PlaneID, distance: int) -> PlaneID:
        """Zero-padded right shift on the caller's fixed spatial interval."""
        width = self.resolve(plane).length
        if type(distance) is not int or distance < 0:
            raise ValueError("plane shift requires a nonnegative distance")
        if distance == 0:
            return plane
        if distance >= width:
            return self.constant(plane.kind, 0, width)
        return self.concat(
            self.constant(plane.kind, 0, distance),
            self.slice(plane, 0, width - distance),
        )

    def carry_prefix(self, domains: PlaneID) -> tuple[PlaneID, int]:
        """Domain grammar supplies all incoming carries and the growth bit."""
        require_endpoint_construction()
        root = self.resolve(domains, "domain")
        # Each record is (word for c=0, exit0, word for c=1, exit1).
        built: dict[int, tuple[words.CanonicalWord, int, words.CanonicalWord, int]] = {}
        pending = [(root, False)]
        while pending:
            node, ready = pending.pop()
            if node.node_id in built:
                continue
            self._tick()
            if node.symbol is not None:
                outputs = []
                exits = []
                for incoming in (0, 1):
                    outgoing = incoming if node.symbol == 1 else int(node.symbol == 2)
                    value = words.run(incoming, 1)
                    if node.length > 1:
                        value = words.concat(
                            value, words.run(outgoing, node.length - 1)
                        )
                    outputs.append(value)
                    exits.append(outgoing)
                result = outputs[0], exits[0], outputs[1], exits[1]
            else:
                if node.left is None or node.right is None:
                    raise ValueError("domain grammar lost its children")
                if not ready:
                    pending.extend(
                        ((node, True), (node.right, False), (node.left, False))
                    )
                    continue
                a, b = built[node.left.node_id], built[node.right.node_id]
                result = (
                    words.concat(a[0], b[0] if a[1] == 0 else b[2]),
                    b[1] if a[1] == 0 else b[3],
                    words.concat(a[2], b[0] if a[3] == 0 else b[2]),
                    b[1] if a[3] == 0 else b[3],
                )
            built[node.node_id] = result
        result = built[root.node_id]
        return self._issue("bool", result[0]), result[1]

    def atom(self, plane: PlaneID, position: int) -> int:
        root = self.resolve(plane)
        if type(position) is not int or not 0 <= position < root.length:
            raise IndexError(position)
        root, _ = self._view(root, position, 1)
        if root.symbol is None:
            raise AssertionError("single-cell plane observation did not reach an atom")
        return root.symbol

    def metrics(self, plane: PlaneID) -> dict[str, int]:
        return words.word_metrics(self.resolve(plane))
