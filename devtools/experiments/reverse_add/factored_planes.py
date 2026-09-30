"""Exact, separately canonical domain/F5/Boolean spatial grammars.

The existing canonical-word owner supplies all rope construction and equality.
Gates walk aligned grammar intervals, never a represented run's positions.
These are explicit execution coordinates, not admitted public point-cache keys.
"""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Callable
from dataclasses import dataclass, field
from itertools import product
from weakref import ReferenceType, WeakValueDictionary, ref

from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn
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
    name: str = field(compare=False)
    inputs: tuple[str, ...]
    output: str
    table: tuple[int | None, ...]
    projection: int | None = field(init=False, compare=False, repr=False)
    constant: bool = field(init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        if (
            type(self.name) is not str
            or type(self.inputs) is not tuple
            or not 0 <= len(self.inputs) <= 4
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
        assignments = tuple(product(*(range(KINDS[k]) for k in self.inputs)))
        projection = next(
            (
                port
                for port in range(len(self.inputs))
                if all(
                    result == values[port]
                    for result, values in zip(self.table, assignments, strict=True)
                )
            ),
            None,
        )
        object.__setattr__(self, "projection", projection)
        object.__setattr__(
            self, "constant", all(v == self.table[0] for v in self.table)
        )

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
_CofactorKey = tuple[PlaneGate, tuple[int, ...]]


class PlaneAlgebra:
    """Transient gate workspace over independently shared canonical ropes.

    Issued handles retain their roots; the registry is weak. Clearing work
    releases temporary gate results, not externally retained carrier planes.
    A bounded source-free cofactor catalog survives those resets. It contains
    complete finite functions, never source occurrences or future observations.
    Work limits apply before each new traversal task, including cache misses.
    This explicit endpoint library has no production resource-audit admission.
    """

    def __init__(
        self,
        *,
        max_work: int = 1_000_000,
        max_cofactors: int = 512,
        max_reuse_entries: int = 4096,
    ) -> None:
        require_endpoint_construction()
        if type(max_work) is not int or max_work <= 0:
            raise ValueError("plane work budget must be positive")
        if type(max_cofactors) is not int or max_cofactors < 0:
            raise ValueError("plane cofactor capacity must be nonnegative")
        if type(max_reuse_entries) is not int or max_reuse_entries < 0:
            raise ValueError("plane reuse capacity must be nonnegative")
        self.owner = object()
        self.max_work = max_work
        self.work = 0
        self.total_work = 0
        self.gate_cache_hits = 0
        self.max_cofactors = max_cofactors
        self.cofactor_cells = 0
        self.cofactor_hits = 0
        self.cofactor_evictions = 0
        self.projection_returns = 0
        self.constant_returns = 0
        self.memo_prune_visits = 0
        self.max_reuse_entries = max_reuse_entries
        self.reuse_lookups = 0
        self.reuse_hits = 0
        self.reuse_evictions = 0
        self.reuse_peak_entries = 0
        self.carry_region_requests = 0
        self.carry_region_hits = 0
        self.carry_region_publications = 0
        self._cofactors: OrderedDict[_CofactorKey, PlaneGate] = OrderedDict()
        # Weak values own no endpoint or intermediate word. Keys contain only
        # exact finite functions and globally unique, validated word IDs.
        self._reuse: OrderedDict[_GateKey, ReferenceType[words.CanonicalWord]] = (
            OrderedDict()
        )
        self._issued: WeakValueDictionary[tuple[str, int], PlaneID] = (
            WeakValueDictionary()
        )
        self._gates: dict[_GateKey, words.CanonicalWord] = {}

    def clear_work(self) -> None:
        self._gates.clear()
        self.work = 0

    def clear_reuse(self) -> None:
        """Bypass arithmetic reuse without invalidating issued source handles."""
        self._reuse.clear()
        self._cofactors.clear()

    def _tick(self) -> None:
        if self.work >= self.max_work:
            raise BlockContextBudgetExceeded("factored plane traversal budget exceeded")
        self.work += 1
        self.total_work += 1

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
        pending = [(gate, views, width, False)]
        results: list[words.CanonicalWord] = []
        while pending:
            operation, current, length, ready = pending.pop()
            current = tuple(self._view(root, start, length) for root, start in current)
            if not ready:
                operation, current = self._cofactor(operation, current)
            key = (
                operation,
                tuple((root.node_id, start) for root, start in current),
                length,
            )
            found = self._gates.get(key)
            if found is not None:
                self.gate_cache_hits += 1
                results.append(found)
                continue
            if not ready and self.max_reuse_entries:
                self.reuse_lookups += 1
                weak_result = self._reuse.get(key)
                found = None if weak_result is None else weak_result()
                if found is not None:
                    self.reuse_hits += 1
                    self._gates[key] = found
                    results.append(found)
                    continue
            self._tick()
            if ready:
                right, left = results.pop(), results.pop()
                result = words.concat(left, right)
            elif operation.projection is not None:
                self.projection_returns += 1
                root, start = current[operation.projection]
                result = self._slice_view(root, start, length)
            elif not current:
                self.constant_returns += 1
                result = words.run(operation.evaluate(()), length)
            elif all(root.symbol is not None for root, _ in current):
                values = tuple(
                    int(root.symbol) for root, _ in current if root.symbol is not None
                )
                result = words.run(operation.evaluate(values), length)
            else:
                split = min(
                    root.left.length - start
                    for root, start in current
                    if root.left is not None
                )
                pending.append((operation, current, length, True))
                pending.append(
                    (
                        operation,
                        tuple((root, start + split) for root, start in current),
                        length - split,
                        False,
                    )
                )
                pending.append((operation, current, split, False))
                continue
            self._gates[key] = result
            if self.max_reuse_entries:
                if (
                    key not in self._reuse
                    and len(self._reuse) >= self.max_reuse_entries
                ):
                    self._reuse.popitem(last=False)
                    self.reuse_evictions += 1
                self._reuse[key] = ref(result)
                self.reuse_peak_entries = max(self.reuse_peak_entries, len(self._reuse))
            results.append(result)
        if len(results) != 1:
            raise AssertionError("plane gate lost its result stack")
        return results[0]

    def _cofactor(
        self, gate: PlaneGate, views: tuple[_View, ...]
    ) -> tuple[PlaneGate, tuple[_View, ...]]:
        """Quotient aligned gate requests by their complete residual function.

        Negative bindings encode constants; nonnegative ones name distinct
        aligned input functions. Repeated views of the same sort are identified
        simultaneously. Undefined table entries remain undefined: neither
        sampled output equality nor an unreachable-input guess permits a merge.
        """
        slots: dict[tuple[str, int, int], int] = {}
        active: list[_View] = []
        kinds: list[str] = []
        binding: list[int] = []
        for kind, (root, start) in zip(gate.inputs, views, strict=True):
            if root.symbol is not None:
                binding.append(-1 - root.symbol)
                continue
            slot_key = kind, root.node_id, start
            slot = slots.get(slot_key)
            if slot is None:
                slot = len(active)
                slots[slot_key] = slot
                active.append((root, start))
                kinds.append(kind)
            binding.append(slot)
        if not gate.constant and tuple(binding) == tuple(range(len(views))):
            return gate, views
        key = gate, tuple(binding)
        residual = self._cofactors.get(key)
        if residual is None:
            table: list[int | None] = []
            for assignment in product(*(range(KINDS[k]) for k in kinds)):
                self._tick()
                self.cofactor_cells += 1
                index = 0
                for kind, port in zip(gate.inputs, binding, strict=True):
                    value = -1 - port if port < 0 else assignment[port]
                    index = index * KINDS[kind] + value
                table.append(gate.table[index])
            if all(value == table[0] for value in table):
                residual = PlaneGate("constant-residual", (), gate.output, (table[0],))
            else:
                residual = PlaneGate(
                    "gate-residual", tuple(kinds), gate.output, tuple(table)
                )
            if self.max_cofactors:
                if len(self._cofactors) == self.max_cofactors:
                    self._cofactors.popitem(last=False)
                    self.cofactor_evictions += 1
                self._cofactors[key] = residual
        else:
            self.cofactor_hits += 1
        return residual, tuple(active) if residual.inputs else ()

    def _slice_view(
        self, root: words.CanonicalWord, start: int, width: int
    ) -> words.CanonicalWord:
        """Share full subtrees; visit only the two clipped interval boundaries."""
        pending = [(root, start, width, False)]
        results: list[words.CanonicalWord] = []
        while pending:
            node, offset, length, ready = pending.pop()
            self._tick()
            if ready:
                after, before = results.pop(), results.pop()
                result = words.concat(before, after)
            elif offset == 0 and length == node.length:
                result = node
            elif node.symbol is not None:
                result = words.run(node.symbol, length)
            else:
                left, right = node.left, node.right
                if left is None or right is None:
                    raise ValueError("plane interval lost its children")
                if offset + length <= left.length:
                    pending.append((left, offset, length, False))
                elif offset >= left.length:
                    pending.append((right, offset - left.length, length, False))
                else:
                    split = left.length - offset
                    pending.extend(
                        (
                            (node, offset, length, True),
                            (right, 0, length - split, False),
                            (left, offset, split, False),
                        )
                    )
                continue
            results.append(result)
        if len(results) != 1:
            raise AssertionError("plane slice lost its result stack")
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

    def carry_prefix(self, domains: PlaneID, incoming: int = 0) -> tuple[PlaneID, int]:
        """Apply the one forward carry monoid to demanded recursive regions.

        A run is pumped through its idempotent carry action. At a join the
        right region receives the left exit. Only that incoming case is built;
        repeated regions with different incoming carries remain distinct memo
        entries. This is a spatial application, not a temporal ActionID.
        """
        require_endpoint_construction()
        if type(incoming) is not int or incoming not in (0, 1):
            raise ValueError("incoming carry must be an exact bit")
        root = self.resolve(domains, "domain")
        built: dict[tuple[int, int], tuple[words.CanonicalWord, int]] = {}
        pending = [(root, incoming, 0)]
        while pending:
            node, entry, stage = pending.pop()
            key = node.node_id, entry
            self._tick()
            if stage == 0:
                self.carry_region_requests += 1
            if key in built:
                self.carry_region_hits += 1
                continue
            if node.symbol is not None:
                action = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)[node.symbol]
                outgoing = apply_carry_fn(action, entry)
                value = words.run(entry, 1)
                if node.length > 1:
                    value = words.concat(value, words.run(outgoing, node.length - 1))
                result = value, outgoing
            else:
                if node.left is None or node.right is None:
                    raise ValueError("domain grammar lost its children")
                if stage == 0:
                    pending.extend(((node, entry, 1), (node.left, entry, 0)))
                    continue
                left, carry = built[node.left.node_id, entry]
                if stage == 1:
                    pending.extend(((node, entry, 2), (node.right, carry, 0)))
                    continue
                right, outgoing = built[node.right.node_id, carry]
                result = words.concat(left, right), outgoing
            built[key] = result
            self.carry_region_publications += 1
        result = built[root.node_id, incoming]
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
