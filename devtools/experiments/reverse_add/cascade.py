"""Canonical dependency-cascade relations for powered transducer contexts.

The grouped arena is a reduced ordered multi-valued decision diagram (MDD):
values sharing the same suffix action are represented by one exact selector,
equal suffixes are hash-consed globally, full-domain levels are eliminated when
the coordinate universe is known, and Cartesian boxes are encoded without
expanding their tuple product.

These objects are compiler/operator metadata only.  They are never part of the
semantic reverse/add state.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator, Sequence
from dataclasses import dataclass
from itertools import pairwise, permutations
from math import prod

from number_compiler.arithmetic.fields.radix import bit_width

_bits = bit_width


def _mask_values(mask: int) -> Iterator[int]:
    mask = int(mask)
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True, slots=True)
class CascadeRelation:
    arity: int
    root: int
    cardinality: int


@dataclass(frozen=True, slots=True)
class CascadeMetrics:
    relations: int
    dependency_nodes: int
    dependency_edges: int
    terminal_nodes: int
    description_bits: int


@dataclass(frozen=True, slots=True)
class SelectorMetrics:
    explicit_values: int
    runs: int
    selector_bits: int


def _selector_metrics_mask(mask: int) -> SelectorMetrics:
    vals = tuple(_mask_values(mask))
    if not vals:
        return SelectorMetrics(0, 0, 0)
    runs = 1 + sum(b != a + 1 for a, b in pairwise(vals))
    width = _bits(vals[-1])
    # Exact selector can be serialized as an explicit list, dense bitset, or
    # inclusive run endpoints.  Charge the cheapest representation.
    bits = min(len(vals) * width, vals[-1] + 1, 2 * runs * width)
    return SelectorMetrics(len(vals), runs, bits)


def group_left_behavior(
    states: Iterable[int],
    step: Callable[[int, int], int | None],
    emit: Callable[[int, int, int], Sequence[int] | None],
    symbol: int,
    right_after: int,
) -> tuple[tuple[int, tuple[int, ...], int], ...]:
    """Group left states by emitted word and successor state."""
    groups: dict[tuple[tuple[int, ...], int], int] = {}
    for left_state in states:
        left_next = step(left_state, symbol)
        if left_next is None:
            continue
        value = emit(left_state, symbol, right_after)
        if value is not None:
            key = (tuple(value), left_next)
            groups[key] = groups.get(key, 0) | (1 << left_state)
    return tuple(
        (mask, value, left_next) for (value, left_next), mask in groups.items()
    )


def _checked_relation_signature(arity: int, relation: CascadeRelation) -> int:
    if relation.arity != int(arity):
        raise ValueError("relation belongs to a different arena")
    return relation.root


class DependencyCascadeArena:
    """Simple hash-consed trie of finite tuple relations.

    Kept as the small baseline/reference representation.  Powered code should
    normally prefer :class:`GroupedDependencyCascadeArena`.
    """

    __slots__ = ("_edge_count", "intern_record", "_nodes", "_relation_roots", "arity")
    EMPTY = 0
    FULL = 1

    def __init__(self, arity: int) -> None:
        arity = int(arity)
        if arity <= 0:
            raise ValueError(arity)
        self.arity = arity
        self.intern_record: dict[tuple[object, ...], int] = {
            ("EMPTY",): 0,
            ("FULL",): 1,
        }
        self._nodes: list[tuple[int, tuple[tuple[int, int], ...]]] = [
            (-1, ()),
            (-2, ()),
        ]
        self._relation_roots: set[int] = set()
        self._edge_count = 0

    def _node(self, level: int, entries: Iterable[tuple[int, int]]) -> int:
        ent = tuple(
            sorted((int(v), int(c)) for v, c in entries if int(c) != self.EMPTY)
        )
        if not ent:
            return self.EMPTY
        key = (int(level), ent)
        old = self.intern_record.get(key)
        if old is not None:
            return old
        node = len(self._nodes)
        self.intern_record[key] = node
        self._nodes.append(key)
        self._edge_count += len(ent)
        return node

    def encode(self, tuples: Iterable[Sequence[int]]) -> CascadeRelation:
        before = self._edge_count
        rows = {tuple(map(int, row)) for row in tuples}
        if any(len(row) != self.arity for row in rows):
            raise ValueError("tuple arity mismatch")
        if not rows:
            self._relation_roots.add(self.EMPTY)
            return CascadeRelation(self.arity, self.EMPTY, 0)

        built: dict[tuple[int, frozenset[tuple[int, ...]]], int] = {}
        start = (0, frozenset(rows))
        stack: list[tuple[int, frozenset[tuple[int, ...]], bool]] = [
            (0, start[1], False)
        ]
        while stack:
            level, subset, ready = stack.pop()
            key = (level, subset)
            if key in built:
                continue
            if level == self.arity:
                built[key] = self.FULL
                continue
            groups: dict[int, frozenset[tuple[int, ...]]] = {}
            mutable: dict[int, set[tuple[int, ...]]] = {}
            for row in subset:
                mutable.setdefault(row[level], set()).add(row)
            groups = {value: frozenset(group) for value, group in mutable.items()}
            if not ready:
                stack.append((level, subset, True))
                for group in reversed(tuple(groups.values())):
                    child_key = (level + 1, group)
                    if child_key not in built:
                        stack.append((level + 1, group, False))
                continue
            built[key] = self._node(
                level,
                ((value, built[(level + 1, group)]) for value, group in groups.items()),
            )
        root = built[start]
        self._relation_roots.add(root)
        from number_compiler.arithmetic.automata.guard import record_cascade_metrics

        record_cascade_metrics(sections=1, dependency_groups=self._edge_count - before)
        return CascadeRelation(self.arity, root, len(rows))

    def iter_tuples(self, relation: CascadeRelation) -> Iterator[tuple[int, ...]]:
        if relation.arity != self.arity:
            raise ValueError("relation belongs to a different arena")
        stack: list[tuple[int, int, tuple[int, ...]]] = [(relation.root, 0, ())]
        while stack:
            node, level, prefix = stack.pop()
            if node == self.EMPTY:
                continue
            if level == self.arity:
                if node != self.FULL:
                    raise AssertionError("invalid terminal")
                yield prefix
                continue
            n = self._nodes[node]
            if n[0] != level:
                raise AssertionError((node, level, n))
            for value, child in reversed(n[1]):
                stack.append((child, level + 1, prefix + (value,)))

    def contains(self, relation: CascadeRelation, row: Sequence[int]) -> bool:
        row = tuple(map(int, row))
        if len(row) != self.arity:
            return False
        node = relation.root
        for level, value in enumerate(row):
            if node in (self.EMPTY, self.FULL):
                return False
            n = self._nodes[node]
            if n[0] != level:
                return False
            node = dict(n[1]).get(value, self.EMPTY)
            if node == self.EMPTY:
                return False
        return node == self.FULL

    def relation_signature(self, relation: CascadeRelation) -> int:
        return _checked_relation_signature(self.arity, relation)

    def metrics(self) -> CascadeMetrics:
        nonterm = max(0, len(self._nodes) - 2)
        id_bits = _bits(max(1, len(self._nodes) - 1))
        value_bits = sum(_bits(v) for node in self._nodes[2:] for v, _ in node[1])
        desc = value_bits + self._edge_count * id_bits + nonterm * _bits(self.arity)
        return CascadeMetrics(
            len(self._relation_roots), nonterm, self._edge_count, 2, desc
        )


class GroupedDependencyCascadeArena:
    """Reduced ordered MDD for exact finite relations.

    ``domains`` optionally fixes the finite coordinate universes.  When supplied,
    a dependency level whose full universe maps to one child is eliminated, the
    standard reduced-decision-diagram rule that removes diamond-shaped no-op
    levels.  Nodes store exact selector bitmasks grouped by shared child.

    ``encode_boxes`` accepts Cartesian boxes (one selector bitmask per coordinate)
    and performs cube subsumption/merging before MDD construction.  It never
    enumerates the Cartesian product represented by a box.
    """

    __slots__ = (
        "_card_cache",
        "_full",
        "_groups",
        "intern_record",
        "_nodes",
        "_roots",
        "_selector_bits",
        "arity",
        "domains",
        "order",
    )
    EMPTY = 0
    FULL = 1

    def __init__(
        self,
        arity: int,
        domains: Sequence[int] | None = None,
        order: Sequence[int] | None = None,
    ) -> None:
        arity = int(arity)
        if arity <= 0:
            raise ValueError(arity)
        self.arity = arity
        if domains is not None:
            domains = tuple(map(int, domains))
            if len(domains) != arity or any(d <= 0 for d in domains):
                raise ValueError(domains)
        if order is None:
            order = tuple(range(arity))
        else:
            order = tuple(map(int, order))
            if sorted(order) != list(range(arity)):
                raise ValueError(order)
        self.domains = domains
        self.order = order
        self._full = (
            None if domains is None else tuple((1 << domains[i]) - 1 for i in order)
        )
        self.intern_record: dict[tuple[object, ...], int] = {
            ("EMPTY",): 0,
            ("FULL",): 1,
        }
        # nonterminal node: (level, ((child, selector_mask), ...))
        self._nodes: list[tuple[int, tuple[tuple[int, int], ...]]] = [
            (-1, ()),
            (-2, ()),
        ]
        self._roots: set[int] = set()
        self._groups = 0
        self._selector_bits = 0
        self._card_cache: dict[tuple[int, int], int] = {}

    def _node(self, level: int, child_masks: dict[int, int]) -> int:
        merged: dict[int, int] = {}
        for child, mask in child_masks.items():
            child, mask = int(child), int(mask)
            if child != self.EMPTY and mask:
                merged[child] = merged.get(child, 0) | mask
        if not merged:
            return self.EMPTY
        # Selectors must be disjoint for a deterministic MDD node.
        seen = 0
        for mask in merged.values():
            if seen & mask:
                raise AssertionError("overlapping grouped selectors")
            seen |= mask
        # Reduced MDD rule: a full-domain don't-care level disappears.
        if self._full is not None and len(merged) == 1:
            child, mask = next(iter(merged.items()))
            if mask == self._full[level]:
                return child
        entries = tuple(sorted(merged.items()))
        key = (int(level), entries)
        old = self.intern_record.get(key)
        if old is not None:
            return old
        node = len(self._nodes)
        self.intern_record[key] = node
        self._nodes.append(key)
        self._groups += len(entries)
        self._selector_bits += sum(
            _selector_metrics_mask(mask).selector_bits for _, mask in entries
        )
        return node

    def _normalize_boxes(
        self, boxes: Iterable[Sequence[int]]
    ) -> tuple[tuple[int, ...], ...]:
        frozen = [tuple(map(int, box)) for box in boxes]
        if any(len(box) != self.arity for box in frozen):
            raise ValueError("box arity mismatch")
        # Reorder coordinates once at the boundary.
        frozen = [tuple(box[i] for i in self.order) for box in frozen]
        if self._full is not None:
            frozen = [
                tuple(mask & self._full[i] for i, mask in enumerate(box))
                for box in frozen
            ]
        work = sorted({box for box in frozen if all(box)})
        if not work:
            return ()

        # Exact cube subsumption. A subset box contributes nothing when a box
        # containing it already exists.
        keep: list[tuple[int, ...]] = []
        for box in sorted(work, key=lambda b: -sum(m.bit_count() for m in b)):
            if any(
                all((m & ~k) == 0 for m, k in zip(box, outer, strict=True))
                for outer in keep
            ):
                continue
            keep.append(box)
        work = keep

        # Merge boxes that differ in only one selector. Iterate to a fixed point;
        # this is the exact Cartesian analogue of reconvergent DAG factoring.
        changed = True
        while changed and len(work) > 1:
            changed = False
            for level in range(self.arity):
                groups: dict[tuple[int, ...], int] = {}
                for box in work:
                    key = box[:level] + box[level + 1 :]
                    groups[key] = groups.get(key, 0) | box[level]
                merged = [
                    key[:level] + (mask,) + key[level:] for key, mask in groups.items()
                ]
                merged = sorted(set(merged))
                if len(merged) < len(work):
                    work = merged
                    changed = True
        return tuple(work)

    @staticmethod
    def _membership_partition(
        active: int, boxes: tuple[tuple[int, ...], ...], level: int
    ) -> dict[int, int]:
        """Return {active-box-subset-bitset: selector-mask} without tuple expansion.

        Dense selectors are split as bitsets.  The number of resulting atoms is
        bounded by the coordinate-domain size, not the Cartesian relation size.
        """
        parts: dict[int, int] = {}
        bitset = int(active)
        while bitset:
            jbit = bitset & -bitset
            j = jbit.bit_length() - 1
            sel = boxes[j][level]
            bitset ^= jbit
            if not parts:
                parts[jbit] = sel
                continue
            new: dict[int, int] = {}
            covered = 0
            for sig, mask in parts.items():
                inter = mask & sel
                if inter:
                    new[sig | jbit] = new.get(sig | jbit, 0) | inter
                    covered |= inter
                diff = mask & ~sel
                if diff:
                    new[sig] = new.get(sig, 0) | diff
            rem = sel & ~covered
            if rem:
                new[jbit] = new.get(jbit, 0) | rem
            parts = new
        return parts

    def encode_boxes(self, boxes: Iterable[Sequence[int]]) -> CascadeRelation:
        before_groups, before_bits = self._groups, self._selector_bits
        boxes = self._normalize_boxes(boxes)
        if not boxes:
            self._roots.add(self.EMPTY)
            return CascadeRelation(self.arity, self.EMPTY, 0)
        all_active = (1 << len(boxes)) - 1
        memo: dict[tuple[int, int], int] = {}

        pending: list[tuple[int, int, bool]] = [(0, all_active, False)]
        while pending:
            level, active, ready = pending.pop()
            key = (level, active)
            if key in memo:
                continue
            if not active:
                memo[key] = self.EMPTY
                continue
            if level == self.arity:
                memo[key] = self.FULL
                continue
            parts = self._membership_partition(active, boxes, level)
            if not ready:
                pending.append((level, active, True))
                for subactive in reversed(tuple(parts)):
                    child_key = (level + 1, subactive)
                    if child_key not in memo:
                        pending.append((level + 1, subactive, False))
                continue
            by_child: dict[int, int] = {}
            for subactive, selector in parts.items():
                child = memo[(level + 1, subactive)]
                if child != self.EMPTY:
                    by_child[child] = by_child.get(child, 0) | selector
            memo[key] = self._node(level, by_child)

        root = memo[(0, all_active)]
        self._roots.add(root)
        cardinality = self._cardinality(root, 0)
        from number_compiler.arithmetic.automata.guard import record_cascade_metrics

        record_cascade_metrics(
            sections=1,
            dependency_groups=self._groups - before_groups,
            selector_bits=self._selector_bits - before_bits,
        )
        return CascadeRelation(self.arity, root, cardinality)

    def encode(self, tuples: Iterable[Sequence[int]]) -> CascadeRelation:
        rows = {tuple(map(int, row)) for row in tuples}
        if any(len(row) != self.arity for row in rows):
            raise ValueError("tuple arity mismatch")
        boxes: list[tuple[int, ...]] = []
        for row in rows:
            box = [0] * self.arity
            for level, original in enumerate(self.order):
                value = row[original]
                if value < 0:
                    raise ValueError(value)
                box[level] = 1 << value
            boxes.append(tuple(box))
        return self.encode_boxes(boxes)

    def _full_mask(self, level: int) -> int:
        if self._full is None:
            raise ValueError("coordinate domains are required for skipped levels")
        return self._full[level]

    def _cardinality(self, node: int, level: int) -> int:
        root_key = (int(node), int(level))
        old = self._card_cache.get(root_key)
        if old is not None:
            return old
        stack: list[tuple[int, int, bool]] = [(root_key[0], root_key[1], False)]
        while stack:
            current, current_level, ready = stack.pop()
            key = (current, current_level)
            if key in self._card_cache:
                continue
            if current == self.EMPTY:
                self._card_cache[key] = 0
                continue
            if current == self.FULL:
                self._card_cache[key] = (
                    1
                    if current_level == self.arity
                    else prod(
                        self._full_mask(i).bit_count()
                        for i in range(current_level, self.arity)
                    )
                )
                continue
            nlevel, entries = self._nodes[current]
            if nlevel < current_level:
                raise AssertionError((current, current_level, nlevel))
            child_level = nlevel + 1
            if not ready:
                stack.append((current, current_level, True))
                for child, _mask in reversed(entries):
                    if (child, child_level) not in self._card_cache:
                        stack.append((child, child_level, False))
                continue
            factor = (
                prod(
                    self._full_mask(i).bit_count() for i in range(current_level, nlevel)
                )
                if nlevel > current_level
                else 1
            )
            self._card_cache[key] = factor * sum(
                mask.bit_count() * self._card_cache[(child, child_level)]
                for child, mask in entries
            )
        return self._card_cache[root_key]

    def iter_boxes(self, relation: CascadeRelation) -> Iterator[tuple[int, ...]]:
        if relation.arity != self.arity:
            raise ValueError("relation belongs to a different arena")
        stack: list[tuple[int, int, tuple[int, ...]]] = [(relation.root, 0, ())]
        while stack:
            node, level, selectors = stack.pop()
            if node == self.EMPTY:
                continue
            if node == self.FULL:
                if level < self.arity:
                    if self._full is None:
                        raise AssertionError("unexpected skipped level without domains")
                    ordered = selectors + self._full[level:]
                else:
                    ordered = selectors
            else:
                nlevel, entries = self._nodes[node]
                prefix = selectors
                if nlevel > level:
                    if self._full is None:
                        raise AssertionError("unexpected skipped level without domains")
                    prefix += self._full[level:nlevel]
                for child, mask in reversed(entries):
                    stack.append((child, nlevel + 1, prefix + (mask,)))
                continue
            # Restore caller/original coordinate order.
            original = [0] * self.arity
            for level, original_idx in enumerate(self.order):
                original[original_idx] = ordered[level]
            yield tuple(original)

    def iter_tuples(self, relation: CascadeRelation) -> Iterator[tuple[int, ...]]:
        for box in self.iter_boxes(relation):
            vals = [tuple(_mask_values(mask)) for mask in box]
            # Small/reference expansion only; powered construction never calls it.
            from itertools import product

            yield from product(*vals)

    def contains(self, relation: CascadeRelation, row: Sequence[int]) -> bool:
        row = tuple(map(int, row))
        if len(row) != self.arity:
            return False
        ordered = tuple(row[i] for i in self.order)
        node, level = relation.root, 0
        while level < self.arity:
            if node == self.EMPTY:
                return False
            if node == self.FULL:
                return True
            nlevel, entries = self._nodes[node]
            # skipped levels are full-domain don't-cares
            if nlevel > level:
                if self._full is None or not (self._full[level] >> ordered[level]) & 1:
                    return False
                level += 1
                continue
            bit = 1 << ordered[level]
            child = self.EMPTY
            for candidate, selector in entries:
                if selector & bit:
                    child = candidate
                    break
            node = child
            level += 1
        return node == self.FULL

    def relation_signature(self, relation: CascadeRelation) -> int:
        return _checked_relation_signature(self.arity, relation)

    def metrics(self) -> CascadeMetrics:
        nonterm = max(0, len(self._nodes) - 2)
        id_bits = _bits(max(1, len(self._nodes) - 1))
        desc = (
            self._selector_bits + self._groups * id_bits + nonterm * _bits(self.arity)
        )
        return CascadeMetrics(len(self._roots), nonterm, self._groups, 2, desc)

    @classmethod
    def best_order_for_boxes(
        cls, domains: Sequence[int], boxes: Iterable[Sequence[int]]
    ) -> tuple[int, tuple[int, ...], GroupedDependencyCascadeArena, CascadeRelation]:
        """Exact small-arity variable-order search by charged MDD description size."""
        domains = tuple(map(int, domains))
        boxes = tuple(tuple(map(int, b)) for b in boxes)
        if len(domains) > 6:
            raise ValueError("factorial order search limited to arity <= 6")
        best = None
        for order in permutations(range(len(domains))):
            arena = cls(len(domains), domains, order)
            rel = arena.encode_boxes(boxes)
            metric = arena.metrics().description_bits
            cand = (metric, order, arena, rel)
            if best is None or cand[:2] < best[:2]:
                best = cand
        assert best is not None
        return best


__all__ = [
    "CascadeMetrics",
    "CascadeRelation",
    "DependencyCascadeArena",
    "GroupedDependencyCascadeArena",
    "SelectorMetrics",
]
