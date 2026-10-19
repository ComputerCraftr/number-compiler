"""Bounded arithmetic circuits for the threshold-geometry experiment.

These IDs are canonical under the implemented algebraic reductions, NOT a
complete extensional function quotient. No BDD or input assignment enumeration
is used during substitution. Unresolved tables and their evaluation are counted.
"""

from __future__ import annotations

from collections.abc import Generator, Iterable, Mapping
from contextlib import contextmanager
from dataclasses import dataclass
from itertools import product

from devtools.verification.growth_coboundary import (
    growth_pair_value,
    growth_symbol_value,
)
from devtools.verification.skew_residue_laws import skew_normalized_digit
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_normalized_pair_sum,
)

# Specialize the existing exact local-law owner on two equal residues. The
# incoming bits matter only through their sum; no geometry coordinate enters
# this value-consumer table. This is not the unequal-residue growth stencil.
MIRROR_PAIR_TABLE = tuple(
    decimal_normalized_pair_sum(r, int(k > 0), r, int(k == 2))
    for r in range(10)
    for k in range(3)
)
MIRROR_DOMAIN_TABLE = tuple(
    tuple(CarryFn).index(value_carry_fn(v, 10)) for v in MIRROR_PAIR_TABLE
)
MIRROR_DOMAIN_ROWS = tuple(
    dict.fromkeys(tuple(MIRROR_DOMAIN_TABLE[3 * r : 3 * r + 3]) for r in range(10))
)
MIRROR_DOMAIN_CLASSES = tuple(
    MIRROR_DOMAIN_ROWS.index(tuple(MIRROR_DOMAIN_TABLE[3 * r : 3 * r + 3]))
    for r in range(10)
)
DECIMAL_SUM_DOMAINS = tuple(
    tuple(CarryFn).index(value_carry_fn(v, 10)) for v in range(19)
)


@dataclass(frozen=True, slots=True)
class Expr:
    owner: object
    index: int


@dataclass(frozen=True, slots=True)
class Node:
    kind: str
    size: int
    args: tuple[int, ...]
    data: tuple[int, ...]
    possible: frozenset[int]


@dataclass(frozen=True, slots=True)
class ConsumerSchema:
    input_size: int
    output_size: int
    table: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class ConsumerSchemaID:
    owner: object
    index: int


class ThresholdExpressions:
    def __init__(self, *, max_nodes: int = 30000, max_work: int = 1000000) -> None:
        require_endpoint_construction()
        if any(type(n) is not int or n < 1 for n in (max_nodes, max_work)):
            raise ValueError("positive expression budgets required")
        self.owner = object()
        self.max_nodes, self.max_work = max_nodes, max_work
        self.nodes: list[Node] = []
        self.keys: dict[tuple[object, ...], int] = {}
        self.schemas: list[ConsumerSchema] = []
        self._schema_keys: dict[ConsumerSchema, int] = {}
        self.work = 0
        self.observed_nodes = 0
        self.observed_tables = 0
        self.bound_reductions = 0
        self.auxiliary_nodes = 0
        self.growth_gauge_alias_hits = 0
        self.substitution_select_branches_skipped = 0
        self.discarded_failed_nodes = 0
        self.discarded_failed_schemas = 0

    @contextmanager
    def construction_transaction(self) -> Generator[None, None, None]:
        """Roll back unpublished expression identities, retaining work charges.

        Used around consumer substitution, which never mutates geometry caches
        or publishes intermediate handles. Existing handles keep their indices.
        Both interning maps must follow their lists back to the checkpoint.
        """
        node_count, schema_count = len(self.nodes), len(self.schemas)
        try:
            yield
        except Exception:
            self.discarded_failed_nodes += len(self.nodes) - node_count
            self.discarded_failed_schemas += len(self.schemas) - schema_count
            del self.nodes[node_count:]
            del self.schemas[schema_count:]
            self.keys = {
                (n.kind, n.size, n.args, n.data): i for i, n in enumerate(self.nodes)
            }
            self._schema_keys = {s: i for i, s in enumerate(self.schemas)}
            raise

    def retain_auxiliary(self) -> None:
        """Charge a derived geometry-cache entry against the same node ceiling."""
        self.tick()
        if len(self.nodes) + len(self.schemas) + self.auxiliary_nodes >= self.max_nodes:
            raise BlockContextBudgetExceeded("threshold auxiliary node budget exceeded")
        self.auxiliary_nodes += 1

    def release_auxiliary(self) -> None:
        if self.auxiliary_nodes <= 0:
            raise AssertionError("unbalanced geometry-cache accounting")
        self.auxiliary_nodes -= 1

    def tick(self, count: int = 1) -> None:
        if type(count) is not int or count < 0:
            raise ValueError("work charges must be exact nonnegative integers")
        self.work += count
        if self.work > self.max_work:
            raise BlockContextBudgetExceeded(
                "threshold expression work budget exceeded"
            )

    def resolve(self, value: Expr) -> Node:
        if (
            type(value) is not Expr
            or value.owner is not self.owner
            or type(value.index) is not int
            or not 0 <= value.index < len(self.nodes)
        ):
            raise ValueError("foreign threshold expression")
        return self.nodes[value.index]

    def handle(self, index: int) -> Expr:
        value = Expr(self.owner, index)
        self.resolve(value)
        return value

    def consumer_program(self, value: Expr) -> tuple[int, int, tuple[int, ...]]:
        """The unary law, with its exact input/output sorts, without operands."""
        schema = self.resolve_schema(self.consumer_schema_id(value))
        return schema.input_size, schema.output_size, schema.table

    def consumer_schema_id(self, value: Expr) -> ConsumerSchemaID:
        node = self.resolve(value)
        if node.kind != "table":
            raise ValueError("expression is not a finite consumer occurrence")
        return ConsumerSchemaID(self.owner, node.data[0])

    def resolve_schema(self, value: ConsumerSchemaID) -> ConsumerSchema:
        if (
            type(value) is not ConsumerSchemaID
            or value.owner is not self.owner
            or type(value.index) is not int
            or not 0 <= value.index < len(self.schemas)
        ):
            raise ValueError("foreign consumer schema")
        return self.schemas[value.index]

    def _intern_schema(
        self, input_size: int, output_size: int, table: tuple[int, ...]
    ) -> int:
        require_endpoint_construction()
        key = ConsumerSchema(input_size, output_size, table)
        found = self._schema_keys.get(key)
        if found is not None:
            return found
        self.tick()
        if len(self.nodes) + len(self.schemas) + self.auxiliary_nodes >= self.max_nodes:
            raise BlockContextBudgetExceeded(
                "threshold expression/schema node budget exceeded"
            )
        result = len(self.schemas)
        self.schemas.append(key)
        self._schema_keys[key] = result
        return result

    def _intern(
        self,
        kind: str,
        size: int,
        args: tuple[int, ...],
        data: tuple[int, ...],
        possible: frozenset[int],
    ) -> Expr:
        require_endpoint_construction()
        self.tick()
        key = kind, size, args, data
        found = self.keys.get(key)
        if found is not None:
            return self.handle(found)
        if len(self.nodes) + len(self.schemas) + self.auxiliary_nodes >= self.max_nodes:
            raise BlockContextBudgetExceeded(
                "threshold expression node budget exceeded"
            )
        index = len(self.nodes)
        self.nodes.append(Node(kind, size, args, data, possible))
        self.keys[key] = index
        return self.handle(index)

    def constant(self, size: int, value: int) -> Expr:
        if (
            type(size) is not int
            or not 1 <= size <= 4096
            or type(value) is not int
            or not 0 <= value < size
        ):
            raise ValueError("constant outside finite sort")
        return self._intern("constant", size, (), (value,), frozenset((value,)))

    def variable(self, size: int, slot: int) -> Expr:
        if (
            type(size) is not int
            or not 1 <= size <= 4096
            or type(slot) is not int
            or slot < 0
        ):
            raise ValueError("invalid finite input coordinate")
        return self._intern("variable", size, (), (slot,), frozenset(range(size)))

    def table(self, value: Expr, size: int, table: tuple[int, ...]) -> Expr:
        node = self.resolve(value)
        if (
            type(table) is not tuple
            or len(table) != node.size
            or type(size) is not int
            or not 1 <= size <= 4096
            or any(type(v) is not int or not 0 <= v < size for v in table)
        ):
            raise ValueError("invalid finite consumer table")
        self.tick(len(table))
        possible = frozenset(table[v] for v in node.possible)
        if len(possible) == 1:
            self.bound_reductions += 1
            return self.constant(size, next(iter(possible)))
        if node.size == size and all(table[v] == v for v in node.possible):
            return value
        # Compose local unary consumers exactly, without a Cartesian context.
        if node.kind == "table":
            table = tuple(table[v] for v in self.schemas[node.data[0]].table)
            value = self.handle(node.args[0])
        schema = self._intern_schema(self.resolve(value).size, size, table)
        return self._intern("table", size, (value.index,), (schema,), possible)

    def affine(
        self, size: int, terms: Iterable[tuple[Expr, int]], offset: int = 0
    ) -> Expr:
        if type(size) is not int or not 1 <= size <= 4096 or type(offset) is not int:
            raise ValueError("invalid modular affine sort")
        coefficients: dict[int, int] = {}
        for expression, coefficient in terms:
            if type(coefficient) is not int:
                raise TypeError("affine coefficient must be exact")
            node = self.resolve(expression)
            self.tick()
            if node.kind == "constant":
                offset += coefficient * node.data[0]
            elif node.kind == "affine" and node.size == size:
                offset += coefficient * node.data[0]
                self.tick(len(node.args))
                for child, scalar in zip(node.args, node.data[1:], strict=True):
                    coefficients[child] = (
                        coefficients.get(child, 0) + coefficient * scalar
                    ) % size
            else:
                coefficients[expression.index] = (
                    coefficients.get(expression.index, 0) + coefficient
                ) % size
        pairs = tuple(sorted((i, c) for i, c in coefficients.items() if c))
        offset %= size
        if not pairs:
            return self.constant(size, offset)
        if len(pairs) == 1 and pairs[0][1] == 1 and offset == 0:
            identity = self.handle(pairs[0][0])
            if self.resolve(identity).size == size:
                return identity
        possible = frozenset((offset,))
        for index, scalar in pairs:
            if len(possible) == size:
                break
            values = self.nodes[index].possible
            self.tick(len(possible) * len(values))
            possible = frozenset(
                (a + scalar * b) % size for a in possible for b in values
            )
        if len(possible) == 1:
            self.bound_reductions += 1
            return self.constant(size, next(iter(possible)))
        return self._intern(
            "affine",
            size,
            tuple(i for i, _ in pairs),
            (offset, *(c for _, c in pairs)),
            possible,
        )

    def select(self, condition: Expr, yes: Expr, no: Expr) -> Expr:
        c, a, b = self.resolve(condition), self.resolve(yes), self.resolve(no)
        if c.size != 2 or a.size != b.size:
            raise ValueError("selection sorts disagree")
        if c.possible == frozenset((1,)) or yes == no:
            return yes
        if c.possible == frozenset((0,)):
            return no
        if (
            a.size == 2
            and a.possible == frozenset((1,))
            and b.possible == frozenset((0,))
        ):
            return condition
        self.tick(len(a.possible) + len(b.possible))
        return self._intern(
            "select",
            a.size,
            (condition.index, yes.index, no.index),
            (),
            a.possible | b.possible,
        )

    def carry_compose(self, after: Expr, before: Expr) -> Expr:
        """Derived domain action, with the existing three-element monoid law."""
        a, b = self.resolve(after), self.resolve(before)
        if a.size != 3 or b.size != 3:
            raise ValueError("carry composition requires domain sorts")
        if a.possible == frozenset((1,)):
            return before
        if 1 not in a.possible or b.possible == frozenset((1,)) or after == before:
            return after
        self.tick(len(a.possible) * len(b.possible))
        domains = tuple(CarryFn)
        possible = frozenset(
            domains.index(compose_carry_fn(domains[x], domains[y]))
            for x in a.possible
            for y in b.possible
        )
        return self._intern(
            "carry_compose", 3, (after.index, before.index), (), possible
        )

    def mirror_pair(
        self, residue: Expr, carry_sum: Expr, *, domain_only: bool = False
    ) -> Expr:
        """Exact normalized pair of one residue under two derived carry ports."""
        r, k = self.resolve(residue), self.resolve(carry_sum)
        if r.size != 10 or k.size != 3:
            raise ValueError("mirror pair requires decimal residue and carry-sum sorts")
        if type(domain_only) is not bool:
            raise ValueError("mirror output projection must be Boolean")
        if domain_only:
            chart = self.table(residue, len(MIRROR_DOMAIN_ROWS), MIRROR_DOMAIN_CLASSES)
            return self._mirror_domain(chart, carry_sum)
        self.tick(len(r.possible) * len(k.possible))
        possible = frozenset(
            MIRROR_PAIR_TABLE[3 * x + y] for x in r.possible for y in k.possible
        )
        if len(possible) == 1:
            self.bound_reductions += 1
            return self.constant(19, next(iter(possible)))
        return self._intern(
            "mirror_pair", 19, (residue.index, carry_sum.index), (), possible
        )

    def _mirror_domain(self, chart: Expr, carry_sum: Expr) -> Expr:
        """The domain consumer sees four residue response rows, not ten values."""
        r, k = self.resolve(chart), self.resolve(carry_sum)
        if r.size != len(MIRROR_DOMAIN_ROWS) or k.size != 3:
            raise ValueError("mirror domain requires response-row and carry-sum sorts")
        if len(r.possible) == 1:
            return self.table(carry_sum, 3, MIRROR_DOMAIN_ROWS[next(iter(r.possible))])
        if len(k.possible) == 1:
            column = next(iter(k.possible))
            return self.table(
                chart, 3, tuple(row[column] for row in MIRROR_DOMAIN_ROWS)
            )
        self.tick(len(r.possible) * len(k.possible))
        possible = frozenset(
            MIRROR_DOMAIN_ROWS[x][y] for x in r.possible for y in k.possible
        )
        if len(possible) == 1:
            return self.constant(3, next(iter(possible)))
        return self._intern(
            "mirror_domain", 3, (chart.index, carry_sum.index), (), possible
        )

    def decimal_sum_domain(self, left: Expr, right: Expr) -> Expr:
        """Classify two normalized residues without retaining a 19-valued sum."""
        a, b = self.resolve(left), self.resolve(right)
        if a.size != 10 or b.size != 10:
            raise ValueError("decimal sum domain requires normalized residue sorts")
        if left == right:
            return self.table(
                left, 3, tuple(DECIMAL_SUM_DOMAINS[2 * v] for v in range(10))
            )
        if len(a.possible) == 1:
            digit = next(iter(a.possible))
            return self.table(
                right, 3, tuple(DECIMAL_SUM_DOMAINS[digit + v] for v in range(10))
            )
        if len(b.possible) == 1:
            digit = next(iter(b.possible))
            return self.table(
                left, 3, tuple(DECIMAL_SUM_DOMAINS[digit + v] for v in range(10))
            )
        self.tick(len(a.possible) * len(b.possible))
        possible = frozenset(
            DECIMAL_SUM_DOMAINS[x + y] for x in a.possible for y in b.possible
        )
        if len(possible) == 1:
            self.bound_reductions += 1
            return self.constant(3, next(iter(possible)))
        return self._intern(
            "decimal_sum_domain",
            3,
            tuple(sorted((left.index, right.index))),
            (),
            possible,
        )

    def growth_symbol(self, residue: Expr, outgoing: Expr, reflected: Expr) -> Expr:
        """Twelve-symbol coboundary chart, before output planes are published."""
        operands = (residue, outgoing, reflected)
        nodes = tuple(self.resolve(v) for v in operands)
        if tuple(n.size for n in nodes) != (10, 2, 2):
            raise ValueError("growth chart needs residue and two derived carry ports")
        # Fuse existing one-variable charts, exactly as unary table composition
        # does. This is a finite local law, not enumeration of source bindings
        # or a Cartesian Boolean context. It recognizes value/carry gauges
        # whose different residue and carry functions cancel in this consumer.
        bases = {
            n.args[0] if n.kind == "table" else v.index
            for v, n in zip(operands, nodes, strict=True)
            if n.kind != "constant"
        }
        if len(bases) == 1:
            base = self.handle(next(iter(bases)))
            size = self.resolve(base).size
            if size <= 12:
                self.tick(3 * size)
                charts = tuple(
                    (n.data[0],) * size
                    if n.kind == "constant"
                    else self.schemas[n.data[0]].table
                    if n.kind == "table"
                    else tuple(range(size))
                    for n in nodes
                )
                result = self.table(
                    base,
                    12,
                    tuple(
                        growth_symbol_value(*values)
                        for values in zip(*charts, strict=True)
                    ),
                )
                self.growth_gauge_alias_hits += int(
                    self.resolve(result).kind == "constant"
                )
                return result
        self.tick(
            len(nodes[0].possible) * len(nodes[1].possible) * len(nodes[2].possible)
        )
        possible = frozenset(
            growth_symbol_value(*v) for v in product(*(n.possible for n in nodes))
        )
        if len(possible) == 1:
            self.bound_reductions += 1
            return self.constant(12, next(iter(possible)))
        return self._intern(
            "growth_symbol", 12, tuple(v.index for v in operands), (), possible
        )

    def growth_domain(self, previous: Expr, current: Expr) -> Expr:
        """Project the radius-one output directly; never publish a source pair."""
        a, b = self.resolve(previous), self.resolve(current)
        if a.size != 12 or b.size != 12:
            raise ValueError("growth domain requires coboundary symbols")
        self.tick(len(a.possible) * len(b.possible))
        possible = frozenset(
            DECIMAL_SUM_DOMAINS[growth_pair_value(x, y) % 19]
            for x in a.possible
            for y in b.possible
        )
        if len(possible) == 1:
            return self.constant(3, next(iter(possible)))
        return self._intern(
            "growth_domain", 3, (previous.index, current.index), (), possible
        )

    def growth_value_plane(self, previous: Expr, current: Expr, modulus: int) -> Expr:
        """Fused affine radius-one transport on coboundary value views.

        F5: q0+q1+d1. F2: q0+q1+d1. The -10*d0 term vanishes
        in both fields. Keeping the projection fused avoids four separately
        bound unary charts per pair; this is a fixed linear local morphism.
        """
        a, b = self.resolve(previous), self.resolve(current)
        if (
            a.size != 12
            or b.size != 12
            or type(modulus) is not int
            or modulus not in (2, 5)
        ):
            raise ValueError("growth value plane requires symbols and F2/F5")
        self.tick(len(a.possible) * len(b.possible))
        possible = frozenset(
            growth_pair_value(x, y) % modulus for x in a.possible for y in b.possible
        )
        if len(possible) == 1:
            return self.constant(modulus, next(iter(possible)))
        return self._intern(
            "growth_value_plane", modulus, (previous.index, current.index), (), possible
        )

    def growth_channels(self, previous: Expr, current: Expr) -> tuple[Expr, Expr, Expr]:
        """Emit the three projections directly from their common quotient."""
        return (
            self.growth_domain(previous, current),
            self.growth_value_plane(previous, current, 5),
            self.growth_value_plane(previous, current, 2),
        )

    def skew_pair_domain(self, *operands: Expr) -> Expr:
        """Consume two geometry/mod9/port views without binding decimal digits.

        The six coordinates remain separate operands. Only the ternary output
        is interned; zero-fiber lifts and reset differences are local values.
        """
        nodes = tuple(self.resolve(v) for v in operands)
        if tuple(n.size for n in nodes) != (3, 9, 2, 3, 9, 2):
            raise ValueError("skew pair requires two domain/mod9/carry triples")
        halves = sorted(
            (tuple(v.index for v in operands[:3]), tuple(v.index for v in operands[3:]))
        )
        arguments = halves[0] + halves[1]
        self.tick()
        found = self.keys.get(("skew_pair_domain", 3, arguments, ()))
        if found is not None:
            return self.handle(found)
        ranges = []
        for offset in (0, 3):
            local = nodes[offset : offset + 3]
            self.tick(
                len(local[0].possible) * len(local[1].possible) * len(local[2].possible)
            )
            ranges.append(
                frozenset(
                    skew_normalized_digit(*values)
                    for values in product(*(n.possible for n in local))
                )
            )
        self.tick(len(ranges[0]) * len(ranges[1]))
        possible = frozenset(
            DECIMAL_SUM_DOMAINS[a + b] for a in ranges[0] for b in ranges[1]
        )
        if len(possible) == 1:
            return self.constant(3, next(iter(possible)))
        return self._intern("skew_pair_domain", 3, arguments, (), possible)

    def carry_apply(self, domain: Expr, incoming: Expr) -> Expr:
        """Carry is an operation on geometry, never a new source variable."""
        d, c = self.resolve(domain), self.resolve(incoming)
        if d.size != 3 or c.size != 2:
            raise ValueError("carry application requires domain and Boolean sorts")
        if d.possible == frozenset((1,)):
            return incoming
        self.tick(len(d.possible) * len(c.possible))
        domains = tuple(CarryFn)
        possible = frozenset(
            apply_carry_fn(domains[x], y) for x in d.possible for y in c.possible
        )
        if len(possible) == 1:
            return self.constant(2, next(iter(possible)))
        return self._intern(
            "carry_apply", 2, (domain.index, incoming.index), (), possible
        )

    def substitute(
        self, roots: tuple[Expr, ...], replacements: Mapping[int, Expr]
    ) -> tuple[Expr, ...]:
        """Pull back demanded roots, resolving selectors before their branches.

        A source-independent selector retains both possible branches. Once
        substitution makes its condition constant, the unchosen branch is not
        visited or rebuilt. No assignments are enumerated to discover a branch.
        """
        for root in roots:
            self.resolve(root)
        for slot, value in replacements.items():
            if type(slot) is not int or slot < 0:
                raise ValueError("invalid substitution slot")
            self.resolve(value)
        built: dict[int, Expr] = {}
        pending = [(root.index, False) for root in roots]
        while pending:
            index, ready = pending.pop()
            if index in built:
                continue
            self.tick()
            node = self.nodes[index]
            if node.kind == "variable":
                if node.data[0] not in replacements:
                    raise ValueError("incomplete temporal substitution")
                result = replacements[node.data[0]]
                if self.resolve(result).size != node.size:
                    raise ValueError("substitution changes coordinate sort")
            elif node.kind == "constant":
                result = self.handle(index)
            elif node.kind == "select":
                condition, yes, no = node.args
                if condition not in built:
                    pending.append((index, True))
                    pending.append((condition, False))
                    continue
                choices = self.resolve(built[condition]).possible
                if len(choices) == 1:
                    selected = yes if 1 in choices else no
                    if selected not in built:
                        pending.append((index, True))
                        pending.append((selected, False))
                        continue
                    result = built[selected]
                    self.substitution_select_branches_skipped += 1
                else:
                    missing = [child for child in (yes, no) if child not in built]
                    if missing:
                        pending.append((index, True))
                        pending.extend((child, False) for child in missing)
                        continue
                    result = self.select(built[condition], built[yes], built[no])
            elif not ready:
                pending.append((index, True))
                pending.extend((child, False) for child in node.args)
                continue
            else:
                children = tuple(built[child] for child in node.args)
                if node.kind == "affine":
                    result = self.affine(
                        node.size,
                        zip(children, node.data[1:], strict=True),
                        node.data[0],
                    )
                elif node.kind == "table":
                    result = self.table(
                        children[0], node.size, self.schemas[node.data[0]].table
                    )
                elif node.kind == "carry_compose":
                    result = self.carry_compose(*children)
                elif node.kind == "carry_apply":
                    result = self.carry_apply(*children)
                elif node.kind == "mirror_pair":
                    result = self.mirror_pair(*children)
                elif node.kind == "mirror_domain":
                    result = self._mirror_domain(*children)
                elif node.kind == "decimal_sum_domain":
                    result = self.decimal_sum_domain(*children)
                elif node.kind == "skew_pair_domain":
                    result = self.skew_pair_domain(*children)
                elif node.kind == "growth_symbol":
                    result = self.growth_symbol(*children)
                elif node.kind == "growth_domain":
                    result = self.growth_domain(*children)
                elif node.kind == "growth_value_plane":
                    result = self.growth_value_plane(
                        children[0], children[1], node.size
                    )
                else:
                    raise AssertionError("unknown threshold expression")
            built[index] = result
        return tuple(built[root.index] for root in roots)

    def reachable(self, roots: tuple[Expr, ...]) -> set[int]:
        for root in roots:
            self.resolve(root)
        seen: set[int] = set()
        pending = [root.index for root in roots]
        while pending:
            index = pending.pop()
            if index in seen:
                continue
            seen.add(index)
            pending.extend(self.nodes[index].args)
        return seen

    def evaluate(
        self, roots: tuple[Expr, ...], binding: tuple[int, ...]
    ) -> tuple[int, ...]:
        """Observe demanded branches, counting only executed consumer work."""
        require_endpoint_construction()
        if type(binding) is not tuple:
            raise ValueError("immutable source binding required")
        for root in roots:
            self.resolve(root)
        values: dict[int, int] = {}
        pending = [root.index for root in roots]
        while pending:
            index = pending.pop()
            if index in values:
                continue
            node = self.nodes[index]
            if node.kind == "select":
                condition, yes, no = node.args
                needed = (
                    (yes if values[condition] else no,)
                    if condition in values
                    else (condition,)
                )
                missing = [i for i in needed if i not in values]
                if missing:
                    pending.append(index)
                    pending.extend(missing)
                    continue
                values[index] = values[yes if values[condition] else no]
                continue
            missing = [i for i in node.args if i not in values]
            if missing:
                pending.append(index)
                pending.extend(missing)
                continue
            args = tuple(values[i] for i in node.args)
            if node.kind == "constant":
                result = node.data[0]
            elif node.kind == "variable":
                if node.data[0] >= len(binding):
                    raise ValueError("incomplete source binding")
                result = binding[node.data[0]]
                if type(result) is not int or not 0 <= result < node.size:
                    raise ValueError("source coordinate outside its sort")
            elif node.kind == "affine":
                result = (
                    node.data[0]
                    + sum(a * c for a, c in zip(args, node.data[1:], strict=True))
                ) % node.size
            elif node.kind == "table":
                result = self.schemas[node.data[0]].table[args[0]]
                self.observed_tables += 1
            elif node.kind == "carry_compose":
                domains = tuple(CarryFn)
                result = domains.index(
                    compose_carry_fn(domains[args[0]], domains[args[1]])
                )
            elif node.kind == "carry_apply":
                result = apply_carry_fn(tuple(CarryFn)[args[0]], args[1])
            elif node.kind == "mirror_pair":
                result = MIRROR_PAIR_TABLE[3 * args[0] + args[1]]
            elif node.kind == "mirror_domain":
                result = MIRROR_DOMAIN_ROWS[args[0]][args[1]]
            elif node.kind == "decimal_sum_domain":
                result = DECIMAL_SUM_DOMAINS[args[0] + args[1]]
            elif node.kind == "skew_pair_domain":
                result = DECIMAL_SUM_DOMAINS[
                    skew_normalized_digit(*args[:3]) + skew_normalized_digit(*args[3:])
                ]
            elif node.kind == "growth_symbol":
                result = growth_symbol_value(*args)
            elif node.kind == "growth_domain":
                result = DECIMAL_SUM_DOMAINS[growth_pair_value(*args) % 19]
            elif node.kind == "growth_value_plane":
                result = growth_pair_value(*args) % node.size
            else:
                raise AssertionError("unknown threshold expression")
            values[index] = result
        self.observed_nodes += len(values)
        return tuple(values[root.index] for root in roots)
