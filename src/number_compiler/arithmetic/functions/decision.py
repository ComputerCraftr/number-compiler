"""Reduced multi-terminal decision DAGs for exact transducer output functions.

The variables are finite coordinates such as ``(left_state, symbol, right_state)``.
Terminals are exact output words (including ``None`` for undefined output).
Internal nodes group selector values that lead to the same child and eliminate a
full-domain level when every value has the same continuation.  Cofactors are
hash-consed back into the same arena, so exact residual-function equality is an
integer root comparison rather than a materialized Cartesian row/column vector.
"""

from __future__ import annotations

import itertools
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from typing import (
    Literal,
    cast,
)

from number_compiler.arithmetic.fields.radix import bit_width

_bits = bit_width

_DecisionNode = (
    tuple[Literal["T"], object] | tuple[Literal["N"], int, tuple[tuple[int, int], ...]]
)


@dataclass
class _BuildFrame:
    level: int
    next_value: int
    by_child: dict[int, int]
    incoming: int | None


def _output_word(value: object) -> tuple[int, ...] | None:
    if value is None:
        return None
    if not isinstance(value, tuple) or any(not isinstance(x, int) for x in value):
        raise TypeError("output terminal must be an integer word or None")
    return cast(tuple[int, ...], value)


def _selector_bits(mask: int) -> int:
    vals = []
    x = int(mask)
    while x:
        b = x & -x
        vals.append(b.bit_length() - 1)
        x ^= b
    if not vals:
        return 0
    runs = 1 + sum(b != a + 1 for a, b in itertools.pairwise(vals))
    width = _bits(vals[-1])
    return min(len(vals) * width, vals[-1] + 1, 2 * runs * width)


@dataclass(frozen=True, slots=True)
class DecisionMetrics:
    terminals: int
    internal_nodes: int
    dependency_groups: int
    selector_bits: int
    exact_probes: int
    description_bits: int
    generator_boxes: int = 0
    normalized_boxes: int = 0


@dataclass(frozen=True, slots=True)
class DecisionStructureMetrics:
    """Root-reachable decision structure independent of terminal serialization."""

    terminals: int
    internal_nodes: int
    dependency_groups: int
    selector_bits: int


class MultiTerminalDecisionArena:
    """Canonical reduced ordered finite-domain decision DAG."""

    __slots__ = (
        "_cofactor_cache",
        "_full",
        "_generator_boxes",
        "_groups",
        "_intern",
        "_length_shape_cache",
        "_length_shape_intern",
        "_minlen_cache",
        "_nodes",
        "_normalized_boxes",
        "_probes",
        "_selector_bits",
        "_term",
        "arity",
        "domains",
        "order",
    )

    def __init__(self, domains: Sequence[int], order: Sequence[int] | None = None):
        domains = tuple(map(int, domains))
        if not domains or any(d <= 0 for d in domains):
            raise ValueError(domains)
        self.domains = domains
        self.arity = len(domains)
        if order is None:
            order = tuple(range(self.arity))
        order = tuple(map(int, order))
        if sorted(order) != list(range(self.arity)):
            raise ValueError(order)
        self.order = order
        self._full = tuple((1 << domains[i]) - 1 for i in order)
        # node = ('T', terminal_value) or ('N', ordered_level, ((child,mask),...))
        self._nodes: list[_DecisionNode] = []
        self._intern: dict[tuple[object, ...], int] = {}
        self._term: dict[object, int] = {}
        self._groups = 0
        self._selector_bits = 0
        self._probes = 0
        self._generator_boxes = 0
        self._normalized_boxes = 0
        self._cofactor_cache: dict[tuple[int, tuple[tuple[int, int], ...]], int] = {}
        self._minlen_cache: dict[int, int | None] = {}
        self._length_shape_cache: dict[int, int] = {}
        self._length_shape_intern: dict[tuple[object, ...], int] = {}

    def terminal(self, value: object) -> int:
        # output words are tuples/None and therefore hashable
        old = self._term.get(value)
        if old is not None:
            return old
        key: _DecisionNode = ("T", value)
        q = len(self._nodes)
        self._nodes.append(key)
        self._intern[key] = q
        self._term[value] = q
        return q

    def _node(self, level: int, child_masks: Mapping[int, int]) -> int:
        merged: dict[int, int] = {}
        for child, mask in child_masks.items():
            if mask:
                merged[int(child)] = merged.get(int(child), 0) | int(mask)
        if not merged:
            raise ValueError("decision node cannot have empty domain")
        seen = 0
        for mask in merged.values():
            if seen & mask:
                raise AssertionError("overlapping selectors")
            seen |= mask
        if seen != self._full[level]:
            raise AssertionError(
                ("decision node must cover full domain", level, seen, self._full[level])
            )
        if len(merged) == 1:
            return next(iter(merged))
        entries = tuple(sorted(merged.items()))
        key: _DecisionNode = ("N", int(level), entries)
        old = self._intern.get(key)
        if old is not None:
            return old
        q = len(self._nodes)
        self._nodes.append(key)
        self._intern[key] = q
        self._groups += len(entries)
        self._selector_bits += sum(_selector_bits(mask) for _, mask in entries)
        return q

    def build(self, resolver: Callable[[tuple[int, ...]], object]) -> int:
        """Build the exact function without retaining a Cartesian leaf table."""
        assignment = [0] * self.arity
        # Each frame is [level, next_value, by_child, incoming_value].  This is
        # the exact depth-first traversal formerly expressed by ``rec``.
        frames: list[_BuildFrame] = [_BuildFrame(0, 0, {}, None)]
        root: int | None = None
        while frames:
            frame = frames[-1]
            level, next_value, by_child, incoming = (
                frame.level,
                frame.next_value,
                frame.by_child,
                frame.incoming,
            )
            if level == self.arity:
                self._probes += 1
                child = self.terminal(resolver(tuple(assignment)))
                frames.pop()
            else:
                original = self.order[level]
                domain = self.domains[original]
                if next_value < domain:
                    assignment[original] = next_value
                    frames[-1].next_value = next_value + 1
                    frames.append(_BuildFrame(level + 1, 0, {}, next_value))
                    continue
                child = self._node(level, by_child)
                frames.pop()
            if not frames:
                root = child
                break
            parent = frames[-1]
            selector_value = incoming
            if selector_value is None:
                raise AssertionError((level, incoming))
            parent_by_child = parent.by_child
            parent_by_child[child] = parent_by_child.get(child, 0) | (
                1 << selector_value
            )
        if root is None:
            raise AssertionError("decision build produced no root")
        return root

    @staticmethod
    def _normalize_labeled_boxes(
        boxes: Iterable[tuple[object, Sequence[int]]], arity: int
    ) -> tuple[tuple[object, ...], ...]:
        """Merge exact same-label Cartesian boxes without tuple expansion.

        This is the canonicalization boundary used by powered composition.  A
        box is ``(terminal, (selector_0, ..., selector_n))`` in *original*
        coordinate order.  Boxes with the same terminal that differ in only one
        selector are unioned to a fixed point.  No merge across terminals is
        permitted.
        """
        work = {
            (terminal,) + tuple(map(int, selectors))
            for terminal, selectors in boxes
            if all(int(mask) != 0 for mask in selectors)
        }
        if any(len(item) != arity + 1 for item in work):
            raise ValueError("labeled-box arity mismatch")
        changed = True
        while changed and len(work) > 1:
            changed = False
            for coordinate in range(arity):
                groups: dict[tuple[object, ...], int] = {}
                for item in work:
                    terminal, selectors = item[0], cast(tuple[int, ...], item[1:])
                    key = (
                        (terminal,)
                        + selectors[:coordinate]
                        + selectors[coordinate + 1 :]
                    )
                    groups[key] = groups.get(key, 0) | selectors[coordinate]
                merged = set()
                for key, mask in groups.items():
                    terminal, rest = key[0], cast(tuple[int, ...], key[1:])
                    selectors = rest[:coordinate] + (mask,) + rest[coordinate:]
                    merged.add((terminal,) + selectors)
                if len(merged) < len(work):
                    work = merged
                    changed = True
        return tuple(sorted(work, key=repr))

    def build_prefix_union(self, prefixes: Iterable[Sequence[int]]) -> int:
        """Boolean membership in finite prefixes, in this arena's variable order.

        Build the sparse trie directly, then use the shared canonical reducer.
        Unconstrained trailing coordinates never enter the construction.
        """
        children: list[dict[int, int]] = [{}]
        depths = [0]
        accepted: set[int] = set()
        for prefix in prefixes:
            values = tuple(prefix)
            if len(values) > self.arity or any(
                type(value) is not int
                or not 0 <= value < self.domains[self.order[level]]
                for level, value in enumerate(values)
            ):
                raise ValueError("prefix outside decision domain")
            node = 0
            for level, value in enumerate(values):
                if node in accepted:
                    break
                child = children[node].get(value)
                if child is None:
                    child = len(children)
                    children[node][value] = child
                    children.append({})
                    depths.append(level + 1)
                node = child
            else:
                accepted.add(node)
        yes, no = self.terminal(True), self.terminal(False)
        reduced: dict[int, int] = {}
        for node in range(len(children) - 1, -1, -1):
            if node in accepted:
                reduced[node] = yes
                continue
            if not children[node]:
                reduced[node] = no
                continue
            level = depths[node]
            by_child = {no: self._full[level]}
            for value, child in children[node].items():
                mask = 1 << value
                by_child[no] &= ~mask
                target = reduced[child]
                by_child[target] = by_child.get(target, 0) | mask
            reduced[node] = self._node(level, by_child)
        return reduced[0]

    def build_labeled_boxes(
        self,
        boxes: Iterable[tuple[object, Sequence[int]]],
        *,
        default: object = None,
        exact_probes: int | None = None,
    ) -> int:
        """Build an exact MTDD directly from labeled Cartesian generators.

        Unlike :meth:`build`, this never enumerates the Cartesian output domain.
        It partitions each finite coordinate by *which canonical boxes contain
        it*, so equal semantic regions are shared before a leaf/context exists.
        Overlapping boxes with different terminals are rejected exactly.
        """
        raw = tuple(
            (terminal, tuple(map(int, selectors))) for terminal, selectors in boxes
        )
        self._generator_boxes += len(raw)
        normalized = self._normalize_labeled_boxes(raw, self.arity)
        self._normalized_boxes += len(normalized)
        if exact_probes is None:
            exact_probes = len(raw)
        self._probes += int(exact_probes)

        # Validate and reorder selectors once.
        ordered: list[tuple[object, tuple[int, ...]]] = []
        for item in normalized:
            terminal, selectors = item[0], cast(tuple[int, ...], item[1:])
            for original, mask in enumerate(selectors):
                if mask < 0 or mask & ~((1 << self.domains[original]) - 1):
                    raise ValueError(("selector outside domain", original, mask))
            ordered.append((terminal, tuple(selectors[i] for i in self.order)))

        default_terminal = self.terminal(default)
        if not ordered:
            return default_terminal

        # coverage[level][value] is a bitset of canonical generator boxes.
        coverage: list[list[int]] = []
        for level, original in enumerate(self.order):
            by_value = [0] * self.domains[original]
            for j, (_, selectors) in enumerate(ordered):
                mask = selectors[level]
                x = mask
                while x:
                    bit = x & -x
                    by_value[bit.bit_length() - 1] |= 1 << j
                    x ^= bit
            coverage.append(by_value)
        labels = tuple(terminal for terminal, _ in ordered)
        all_active = (1 << len(ordered)) - 1
        memo: dict[tuple[int, int], int] = {}
        leaf_cache: dict[int, int] = {0: default_terminal}

        def leaf(active: int) -> int:
            old = leaf_cache.get(active)
            if old is not None:
                return old
            x = active
            terminal: object = ...
            while x:
                bit = x & -x
                j = bit.bit_length() - 1
                x ^= bit
                value = labels[j]
                if terminal is ...:
                    terminal = value
                elif terminal != value:
                    raise AssertionError("overlapping canonical output boxes disagree")
            out = default_terminal if terminal is ... else self.terminal(terminal)
            leaf_cache[active] = out
            return out

        stack: list[tuple[int, int, bool]] = [(0, all_active, False)]
        while stack:
            level, active, ready = stack.pop()
            key = (level, active)
            if key in memo:
                continue
            if level == self.arity:
                memo[key] = leaf(active)
                continue
            if not ready:
                stack.append((level, active, True))
                for covered in reversed(coverage[level]):
                    sub = active & covered
                    if sub and (level + 1, sub) not in memo:
                        stack.append((level + 1, sub, False))
                continue
            by_child: dict[int, int] = {}
            for value, covered in enumerate(coverage[level]):
                sub = active & covered
                child = memo[(level + 1, sub)] if sub else default_terminal
                by_child[child] = by_child.get(child, 0) | (1 << value)
            memo[key] = self._node(level, by_child)
        return memo[(0, all_active)]

    def project_values(
        self, root: int, selections: Sequence[Sequence[int]]
    ) -> tuple[MultiTerminalDecisionArena, int]:
        """Project/relabel an MTDD onto selected source-coordinate values.

        ``selections[i][new] == old``.  The result is a fresh canonical arena
        over the smaller domains and is built structurally from the existing DAG;
        no output context is evaluated.
        """
        selections = tuple(tuple(map(int, xs)) for xs in selections)
        if len(selections) != self.arity or any(not xs for xs in selections):
            raise ValueError("one nonempty selection list per coordinate required")
        for coordinate, xs in enumerate(selections):
            if any(x < 0 or x >= self.domains[coordinate] for x in xs):
                raise ValueError((coordinate, xs))
        out = MultiTerminalDecisionArena(
            tuple(len(xs) for xs in selections), self.order
        )
        memo: dict[tuple[int, int], int] = {}

        def remap_mask(original: int, old_mask: int) -> int:
            mask = 0
            for new_value, old_value in enumerate(selections[original]):
                if old_mask & (1 << old_value):
                    mask |= 1 << new_value
            return mask

        start = (int(root), 0)
        stack: list[tuple[int, int, bool]] = [(start[0], start[1], False)]
        while stack:
            node, level, ready = stack.pop()
            key = (node, level)
            if key in memo:
                continue
            n = self._nodes[node]
            if n[0] == "T":
                memo[key] = out.terminal(n[1])
                continue
            if level >= self.arity:
                raise AssertionError((node, level))
            _, nlevel, entries = n
            deps: list[tuple[int, int]] = []
            if nlevel > level:
                deps.append((node, level + 1))
            elif nlevel < level:
                raise AssertionError((node, level, nlevel))
            else:
                original = self.order[level]
                deps.extend(
                    (child, level + 1)
                    for child, old_mask in entries
                    if remap_mask(original, old_mask)
                )
            if not ready:
                stack.append((node, level, True))
                for dep_node, dep_level in reversed(deps):
                    if (dep_node, dep_level) not in memo:
                        stack.append((dep_node, dep_level, False))
                continue
            if nlevel > level:
                memo[key] = memo[(node, level + 1)]
                continue
            original = self.order[level]
            by_child: dict[int, int] = {}
            for child, old_mask in entries:
                new_mask = remap_mask(original, old_mask)
                if not new_mask:
                    continue
                c = memo[(child, level + 1)]
                by_child[c] = by_child.get(c, 0) | new_mask
            if not by_child:
                raise AssertionError("projection removed full decision domain")
            memo[key] = out._node(level, by_child)
        return out, memo[start]

    def relabel_terminals(
        self, root: int, relabel: Callable[[object], object]
    ) -> tuple[MultiTerminalDecisionArena, int]:
        """Relabel terminal observations and canonically reduce the same DAG.

        This is the exact Moore-projection operation for a fixed ordered input
        language.  Internal source predicates are preserved, while terminal
        distinctions hidden by ``relabel`` disappear immediately through the
        destination arena's hash-consed reducer.  No Cartesian input row is
        enumerated and no source/output evaluator is called.

        In particular, callers can keep a rich audit terminal in one relation
        and derive a smaller consumer quotient (for example endpoint-only or
        endpoint-plus-clock) without allowing audit provenance to become part
        of semantic action identity.
        """
        if not callable(relabel):
            raise TypeError("terminal relabeler must be callable")
        if type(root) is not int:
            raise TypeError("decision root must be an exact integer")
        if not 0 <= root < len(self._nodes):
            raise ValueError("decision root lies outside this arena")
        out = MultiTerminalDecisionArena(self.domains, self.order)
        memo: dict[int, int] = {}
        stack: list[tuple[int, bool]] = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node in memo:
                continue
            record = self._nodes[node]
            if record[0] == "T":
                memo[node] = out.terminal(relabel(record[1]))
                continue
            if not ready:
                stack.append((node, True))
                for child, _mask in reversed(record[2]):
                    if child not in memo:
                        stack.append((child, False))
                continue
            by_child: dict[int, int] = {}
            for child, mask in record[2]:
                mapped = memo[child]
                by_child[mapped] = by_child.get(mapped, 0) | mask
            memo[node] = out._node(record[1], by_child)
        return out, memo[root]

    def _select(self, node: int, ordered_level: int, value: int) -> int:
        n = self._nodes[int(node)]
        if n[0] == "T":
            return node
        _, level, entries = n
        if level > ordered_level:
            # This level was reduced as a don't-care.
            return node
        if level < ordered_level:
            raise ValueError("assignment skips an unresolved earlier variable")
        bit = 1 << int(value)
        for child, mask in entries:
            if mask & bit:
                return child
        raise AssertionError((node, ordered_level, value))

    def cofactor(self, root: int, assignments: Mapping[int, int]) -> int:
        """Restrict original-coordinate variables and reduce canonically."""
        items = tuple(sorted((int(k), int(v)) for k, v in assignments.items()))
        for k, v in items:
            if not 0 <= k < self.arity or not 0 <= v < self.domains[k]:
                raise ValueError((k, v))
        key = (int(root), items)
        old = self._cofactor_cache.get(key)
        if old is not None:
            return old
        amap = dict(items)
        memo: dict[tuple[int, int], int] = {}
        start = (int(root), 0)
        stack: list[tuple[int, int, bool]] = [(start[0], start[1], False)]
        while stack:
            node, level, ready = stack.pop()
            mk = (node, level)
            if mk in memo:
                continue
            n = self._nodes[node]
            if n[0] == "T" or level == self.arity:
                memo[mk] = node
                continue
            original = self.order[level]
            nlevel = n[1]
            if nlevel > level:
                deps = [(node, level + 1)]
            elif original in amap:
                deps = [(self._select(node, level, amap[original]), level + 1)]
            else:
                deps = [(child, level + 1) for child, _mask in n[2]]
            if not ready:
                stack.append((node, level, True))
                for dep_node, dep_level in reversed(deps):
                    if (dep_node, dep_level) not in memo:
                        stack.append((dep_node, dep_level, False))
                continue
            if nlevel > level:
                memo[mk] = memo[(node, level + 1)]
            elif original in amap:
                selected = self._select(node, level, amap[original])
                memo[mk] = memo[(selected, level + 1)]
            else:
                by_child: dict[int, int] = {}
                for child, mask in n[2]:
                    c = memo[(child, level + 1)]
                    by_child[c] = by_child.get(c, 0) | mask
                memo[mk] = self._node(level, by_child)
        result = memo[start]
        self._cofactor_cache[key] = result
        return result

    def iter_labeled_boxes(
        self, root: int, *, include_default: bool = True
    ) -> Iterator[tuple[object, tuple[int, ...]]]:
        """Yield exact disjoint terminal Cartesian boxes for ``root``.

        The MTDD is already a partition of the finite coordinate domain.  This
        iterator exposes that partition without evaluating any Cartesian leaf.
        Selectors are returned in the *original* coordinate order, so callers
        can intersect/project them directly with other canonical relations.
        """
        full_original = tuple((1 << d) - 1 for d in self.domains)
        stack: list[tuple[int, tuple[int, ...]]] = [(int(root), full_original)]
        while stack:
            node, selectors = stack.pop()
            n = self._nodes[node]
            if n[0] == "T":
                if include_default or n[1] is not None:
                    yield n[1], selectors
                continue
            _, level, entries = n
            original = self.order[level]
            for child, mask in reversed(entries):
                updated = list(selectors)
                updated[original] = int(mask)
                stack.append((child, tuple(updated)))

    def evaluate(self, root: int, coordinates: Sequence[int]) -> object:
        coordinates = tuple(map(int, coordinates))
        if len(coordinates) != self.arity:
            raise ValueError(coordinates)
        node = int(root)
        level = 0
        while True:
            n = self._nodes[node]
            if n[0] == "T":
                return n[1]
            _, nlevel, entries = n
            if nlevel < level:
                raise AssertionError((node, level, nlevel))
            level = nlevel
            original = self.order[level]
            value = coordinates[original]
            bit = 1 << value
            for child, mask in entries:
                if mask & bit:
                    node = child
                    level += 1
                    break
            else:
                raise AssertionError((node, value))

    def terminal_value(self, root: int) -> object:
        """Return a terminal value, rejecting a root with unresolved inputs."""
        if type(root) is not int:
            raise TypeError("decision root must be an exact integer")
        if not 0 <= root < len(self._nodes):
            raise ValueError("decision root lies outside this arena")
        node = self._nodes[root]
        if node[0] != "T":
            raise ValueError("decision root still depends on input coordinates")
        return node[1]

    def structural_metrics(self, root: int) -> DecisionStructureMetrics:
        """Measure the root-reachable DAG without interpreting terminal values."""
        if type(root) is not int:
            raise TypeError("decision root must be an exact integer")
        if not 0 <= root < len(self._nodes):
            raise ValueError("decision root lies outside this arena")
        pending = [root]
        seen: set[int] = set()
        terminals = internal = groups = selector_bits = 0
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            seen.add(node)
            record = self._nodes[node]
            if record[0] == "T":
                terminals += 1
                continue
            internal += 1
            groups += len(record[2])
            selector_bits += sum(_selector_bits(mask) for _child, mask in record[2])
            pending.extend(child for child, _mask in record[2])
        return DecisionStructureMetrics(terminals, internal, groups, selector_bits)

    def min_output_length(self, root: int) -> int | None:
        root = int(root)
        old = self._minlen_cache.get(root, ...)
        if old is not ...:
            return old
        stack: list[tuple[int, bool]] = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node in self._minlen_cache:
                continue
            n = self._nodes[node]
            if n[0] == "T":
                value = _output_word(n[1])
                self._minlen_cache[node] = None if value is None else len(value)
                continue
            if not ready:
                stack.append((node, True))
                for child, _mask in reversed(n[2]):
                    if child not in self._minlen_cache:
                        stack.append((child, False))
                continue
            finite = [self._minlen_cache[child] for child, _ in n[2]]
            finite_lengths = [x for x in finite if x is not None]
            self._minlen_cache[node] = min(finite_lengths) if finite_lengths else None
        return self._minlen_cache[root]

    def tropical_length_shape(self, root: int) -> int:
        """Canonical projective output-length shape used only as a pre-signature."""
        old = self._length_shape_cache.get(int(root))
        if old is not None:
            return old
        root = int(root)
        base = self.min_output_length(root)
        built: dict[int, int] = {}
        stack: list[tuple[int, bool]] = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node in built:
                continue
            n = self._nodes[node]
            if n[0] == "T":
                v = _output_word(n[1])
                length = None if v is None else len(v)
                shape_key: tuple[object, ...] = (
                    "T",
                    None if length is None or base is None else length - base,
                )
            else:
                if not ready:
                    stack.append((node, True))
                    for child, _mask in reversed(n[2]):
                        if child not in built:
                            stack.append((child, False))
                    continue
                shape_key = (
                    "N",
                    n[1],
                    tuple((built[child], mask) for child, mask in n[2]),
                )
            old2 = self._length_shape_intern.get(shape_key)
            if old2 is None:
                old2 = len(self._length_shape_intern)
                self._length_shape_intern[shape_key] = old2
            built[node] = old2
        result = built[root]
        self._length_shape_cache[root] = result
        return result

    def metrics(self) -> DecisionMetrics:
        terminals = sum(n[0] == "T" for n in self._nodes)
        internals = len(self._nodes) - terminals
        idbits = _bits(max(1, len(self._nodes) - 1))
        terminal_bits = 0
        for n in self._nodes:
            if n[0] == "T":
                v = _output_word(n[1])
                terminal_bits += 1 if v is None else 1 + sum(_bits(x) for x in v)
        desc = (
            terminal_bits
            + self._selector_bits
            + self._groups * idbits
            + internals * _bits(self.arity)
        )
        return DecisionMetrics(
            terminals,
            internals,
            self._groups,
            self._selector_bits,
            self._probes,
            desc,
            self._generator_boxes,
            self._normalized_boxes,
        )


@dataclass(slots=True)
class CanonicalOutputRelation:
    """Exact canonical output function attached to a bimachine.

    Coordinates in the decision arena are dense indices; these maps keep the
    external DFA/symbol ids independent of that representation.
    """

    arena: MultiTerminalDecisionArena
    root: int
    left_states: tuple[int, ...]
    alphabet: tuple[int, ...]
    right_states: tuple[int, ...]

    def __post_init__(self) -> None:
        self._left = {q: i for i, q in enumerate(self.left_states)}
        self._symbol = {a: i for i, a in enumerate(self.alphabet)}
        self._right = {q: i for i, q in enumerate(self.right_states)}

    _left: dict[int, int] = field(init=False)
    _symbol: dict[int, int] = field(init=False)
    _right: dict[int, int] = field(init=False)

    def emit(self, left: int, symbol: int, right: int) -> tuple[int, ...] | None:
        return _output_word(
            self.arena.evaluate(
                self.root,
                (
                    self._left[int(left)],
                    self._symbol[int(symbol)],
                    self._right[int(right)],
                ),
            )
        )

    def cofactor(self, assignments: Mapping[int, int]) -> int:
        dense = {}
        for coordinate, value in assignments.items():
            coordinate = int(coordinate)
            value = int(value)
            if coordinate == 0:
                dense[0] = self._left[value]
            elif coordinate == 1:
                dense[1] = self._symbol[value]
            elif coordinate == 2:
                dense[2] = self._right[value]
            else:
                raise ValueError(coordinate)
        return self.arena.cofactor(self.root, dense)

    def iter_boxes(
        self, *, symbol: int | None = None, include_undefined: bool = False
    ) -> Iterator[tuple[tuple[int, ...] | None, tuple[int, int, int]]]:
        """Yield exact ``(output,(left_mask,symbol_mask,right_mask))`` regions.

        When ``symbol`` is supplied, the symbol coordinate is restricted without
        enumerating left/right contexts.  The returned masks use external DFA
        state ids, which are dense for production machines.
        """
        symbol_dense = None if symbol is None else self._symbol[int(symbol)]
        for output, selectors in self.arena.iter_labeled_boxes(
            self.root, include_default=include_undefined
        ):
            lm, am, rm = selectors
            if symbol_dense is not None:
                bit = 1 << symbol_dense
                if not (am & bit):
                    continue
                am = bit
            if output is None and not include_undefined:
                continue
            yield _output_word(output), (lm, am, rm)

    def project(
        self,
        left_old: Sequence[int],
        right_old: Sequence[int],
        *,
        new_left: Sequence[int] | None = None,
        new_right: Sequence[int] | None = None,
    ) -> CanonicalOutputRelation:
        left_old = tuple(map(int, left_old))
        right_old = tuple(map(int, right_old))
        selections = (
            tuple(self._left[q] for q in left_old),
            tuple(range(len(self.alphabet))),
            tuple(self._right[q] for q in right_old),
        )
        arena, root = self.arena.project_values(self.root, selections)
        if new_left is None:
            new_left = tuple(range(len(left_old)))
        if new_right is None:
            new_right = tuple(range(len(right_old)))
        return CanonicalOutputRelation(
            arena,
            root,
            tuple(map(int, new_left)),
            self.alphabet,
            tuple(map(int, new_right)),
        )


__all__ = [
    "CanonicalOutputRelation",
    "DecisionMetrics",
    "DecisionStructureMetrics",
    "MultiTerminalDecisionArena",
]
