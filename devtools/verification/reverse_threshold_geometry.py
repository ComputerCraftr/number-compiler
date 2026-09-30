"""Recursive spatial threshold cells over exact arithmetic expressions.

Range proofs can classify a whole interval before splitting. Mixed intervals
retain unresolved local consumers. Spatial equality is exact for the resulting
expression word; expression equality is only the sound reductions of its owner,
not a complete contextual syntactic quotient.
"""

from __future__ import annotations

from dataclasses import dataclass
from weakref import ReferenceType, finalize, ref

from devtools.experiments.reverse_add.factored_planes import PlaneAlgebra
from devtools.verification.threshold_expressions import (
    DECIMAL_SUM_DOMAINS,
    Expr,
    ThresholdExpressions,
)
from number_compiler.arithmetic.automata import program_word as words

DOMAIN_TABLE = DECIMAL_SUM_DOMAINS


def _release_carry_cache(
    actions: dict[int, Expr],
    watches: dict[int, ReferenceType[words.CanonicalWord]],
    expressions: ThresholdExpressions,
) -> None:
    for _ in range(len(actions)):
        expressions.release_auxiliary()
    actions.clear()
    watches.clear()


@dataclass(frozen=True, slots=True)
class ThresholdGeometryID:
    owner: object
    word: words.CanonicalWord


class ThresholdGeometry:
    def __init__(self, expressions: ThresholdExpressions) -> None:
        self.expressions = expressions
        self.owner = object()
        self.visits = 0
        self.uniform_proofs = 0
        self.local_consumers = 0
        self._carry_actions: dict[int, Expr] = {}
        self._carry_watches: dict[int, ReferenceType[words.CanonicalWord]] = {}
        finalize(
            self,
            _release_carry_cache,
            self._carry_actions,
            self._carry_watches,
            expressions,
        )

    def _remember_carry(self, root: words.CanonicalWord, action: Expr) -> None:
        self.expressions.retain_auxiliary()
        index = root.node_id
        actions, watches, expressions = (
            self._carry_actions,
            self._carry_watches,
            self.expressions,
        )

        def expired(_reference: ReferenceType[words.CanonicalWord]) -> None:
            actions.pop(index)
            watches.pop(index)
            expressions.release_auxiliary()

        self._carry_actions[index] = action
        self._carry_watches[index] = ref(root, expired)

    def from_domains(self, domains: tuple[Expr, ...]) -> ThresholdGeometryID:
        if type(domains) is not tuple or not domains:
            raise ValueError("nonempty immutable domain coordinates required")
        self.expressions.tick(len(domains))
        if any(self.expressions.resolve(d).size != 3 for d in domains):
            raise ValueError("geometry requires domain expressions")
        return ThresholdGeometryID(
            self.owner, words.from_values(d.index for d in domains)
        )

    def _check(self, geometry: ThresholdGeometryID) -> None:
        if (
            type(geometry) is not ThresholdGeometryID
            or geometry.owner is not self.owner
        ):
            raise ValueError("foreign threshold geometry")
        words._validate_word(geometry.word)

    def _carry_summary(self, root: words.CanonicalWord) -> Expr:
        """Memoized projection of the immutable geometry DAG, not state."""
        e = self.expressions
        pending = [(root, False)]
        while pending:
            node, ready = pending.pop()
            if node.node_id in self._carry_actions:
                continue
            e.tick()
            if node.symbol is not None:
                result = e.handle(node.symbol)
                if e.resolve(result).size != 3:
                    raise ValueError("geometry requires domain expressions")
                # Every carry monoid element is idempotent: a run needs one action.
            else:
                if node.left is None or node.right is None:
                    raise ValueError("empty domain geometry")
                if not ready:
                    pending.extend(
                        ((node, True), (node.right, False), (node.left, False))
                    )
                    continue
                result = e.carry_compose(
                    self._carry_actions[node.right.node_id],
                    self._carry_actions[node.left.node_id],
                )
            self._remember_carry(node, result)
        return self._carry_actions[root.node_id]

    def prefix_action(self, geometry: ThresholdGeometryID, stop: int) -> Expr:
        """Derive [0,stop)'s action; descend one path after shared summaries."""
        self._check(geometry)
        root = geometry.word
        if type(stop) is not int or not 0 <= stop <= root.length:
            raise ValueError("carry boundary outside domain geometry")
        e = self.expressions
        result = e.constant(3, 1)
        while stop:
            e.tick()
            if stop == root.length or root.symbol is not None:
                result = e.carry_compose(self._carry_summary(root), result)
                break
            left, right = root.left, root.right
            if left is None or right is None:
                raise ValueError("domain geometry lost its children")
            if stop <= left.length:
                root = left
            else:
                result = e.carry_compose(self._carry_summary(left), result)
                stop -= left.length
                root = right
        return result

    def carry_at(
        self, geometry: ThresholdGeometryID, position: int, incoming: Expr
    ) -> Expr:
        if self.expressions.resolve(incoming).size != 2:
            raise ValueError("carry query requires a Boolean incoming port")
        return self.expressions.carry_apply(
            self.prefix_action(geometry, position), incoming
        )

    def _bounds(self, root: words.CanonicalWord) -> dict[int, tuple[int, int]]:
        bounds: dict[int, tuple[int, int]] = {}
        pending = [(root, False)]
        while pending:
            node, ready = pending.pop()
            if node.node_id in bounds:
                continue
            self.expressions.tick()
            if node.symbol is not None:
                expression = self.expressions.resolve(
                    self.expressions.handle(node.symbol)
                )
                if expression.size != 10:
                    raise ValueError("threshold inputs must be local decimal residues")
                value = min(expression.possible), max(expression.possible)
            else:
                if node.left is None or node.right is None:
                    raise ValueError("empty threshold interval")
                if not ready:
                    pending.extend(
                        ((node, True), (node.right, False), (node.left, False))
                    )
                    continue
                a, b = bounds[node.left.node_id], bounds[node.right.node_id]
                value = min(a[0], b[0]), max(a[1], b[1])
            bounds[node.node_id] = value
        return bounds

    def _compare(
        self, left: words.CanonicalWord, right: words.CanonicalWord
    ) -> ThresholdGeometryID:
        if left.length != right.length or not left.length:
            raise ValueError("threshold operands require aligned nonempty cells")
        bounds = self._bounds(left) | self._bounds(right)
        pending = [(left, 0, right, 0, left.length, False)]
        results: list[words.CanonicalWord] = []
        memo: dict[tuple[int, int, int, int, int], words.CanonicalWord] = {}
        e = self.expressions
        while pending:
            a, i, b, j, width, ready = pending.pop()
            a, i = PlaneAlgebra._view(a, i, width)
            b, j = PlaneAlgebra._view(b, j, width)
            key = a.node_id, i, b.node_id, j, width
            if key in memo:
                results.append(memo[key])
                continue
            e.tick()
            self.visits += 1
            low = bounds[a.node_id][0] + bounds[b.node_id][0]
            high = bounds[a.node_id][1] + bounds[b.node_id][1]
            if ready:
                tail, head = results.pop(), results.pop()
                result = words.concat(head, tail)
            elif high < 9 or low > 9 or low == high == 9:
                domain = 0 if high < 9 else 2 if low > 9 else 1
                result = words.run(e.constant(3, domain).index, width)
                self.uniform_proofs += 1
            elif a.symbol is not None and b.symbol is not None:
                classified = e.decimal_sum_domain(
                    e.handle(a.symbol), e.handle(b.symbol)
                )
                result = words.run(classified.index, width)
                self.local_consumers += 1
            else:
                split = min(
                    root.left.length - start
                    for root, start in ((a, i), (b, j))
                    if root.left is not None
                )
                pending.extend(
                    (
                        (a, i, b, j, width, True),
                        (a, i + split, b, j + split, width - split, False),
                        (a, i, b, j, split, False),
                    )
                )
                continue
            memo[key] = result
            results.append(result)
        if len(results) != 1:
            raise AssertionError("threshold traversal lost its result")
        return ThresholdGeometryID(self.owner, results[0])

    def uniform(self, left: Expr, right: Expr, width: int) -> ThresholdGeometryID:
        self.expressions.resolve(left)
        self.expressions.resolve(right)
        if type(width) is not int or width < 1:
            raise ValueError("positive spatial width required")
        return self._compare(
            words.run(left.index, width), words.run(right.index, width)
        )

    def compare(
        self, left: tuple[Expr, ...], right: tuple[Expr, ...]
    ) -> ThresholdGeometryID:
        if (
            type(left) is not tuple
            or type(right) is not tuple
            or not 1 <= len(left) <= 4096
            or len(left) != len(right)
        ):
            raise ValueError("bounded immutable aligned expression words required")
        self.expressions.tick(len(left) + len(right))
        for value in (*left, *right):
            self.expressions.resolve(value)
        return self._compare(
            words.from_values(v.index for v in left),
            words.from_values(v.index for v in right),
        )

    def coordinates(self, geometry: ThresholdGeometryID) -> tuple[Expr, ...]:
        self._check(geometry)
        # Only the bounded action interface requests coordinates. Uniform-cell
        # proofs and their metrics never expand a represented run.
        if geometry.word.length > 4096:
            raise ValueError("geometry coordinate export exceeds bounded interface")
        return tuple(
            self.expressions.handle(v)
            for v, count in words.iter_runs(geometry.word)
            for _ in range(count)
        )
