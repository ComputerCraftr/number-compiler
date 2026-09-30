"""Source-independent reverse/add action on a bounded complete spatial context.

All coordinates are finite functions, not bound values. Overflow is undefined
and is pulled through every temporal composition. This deliberately exposes
the cost of a flat interface; it is not a claimed recursive spatial quotient.
"""

from __future__ import annotations

from devtools.experiments.reverse_add.cocycle_temporal import (
    CocycleAction,
    CocycleTemporalArena,
)
from devtools.experiments.reverse_add.factored_carrier import DOMAINS
from devtools.experiments.reverse_add.threshold_cocycle import (
    ResidueMorphism,
    ThresholdCocycleArena,
    ThresholdCocycleResidualID,
)
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_coordinates,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.active_output import CARRY_ACTION, F5


class BoundedReverseCocycle:
    def __init__(
        self,
        capacity: int,
        *,
        max_nodes: int = 30000,
        max_entries: int = 100000,
        symmetric: bool = False,
    ) -> None:
        if type(capacity) is not int or not 1 <= capacity <= 4096:
            raise ValueError("bounded cocycle capacity must lie in 1..4096")
        if type(symmetric) is not bool:
            raise TypeError("symmetric context selection requires a Boolean")
        self.capacity = capacity
        self.symmetric = symmetric
        self.orbit_capacity = (capacity + 1) // 2 if symmetric else capacity
        self.bits = BitFunctionArena(ResourceLedger(max_nodes, max_entries))
        self.cocycles = ThresholdCocycleArena(self.bits)
        self.temporal = CocycleTemporalArena(self.cocycles)
        self.width_sort = AtomSort("bounded-cocycle-width", capacity + 1)
        extent = FinitePort(PortVariable(0, 0, "extent", 0), capacity + 1)
        self.ports = (
            extent,
            *(
                FinitePort(PortVariable(0, i + 1, role, 0), sort.cardinality)
                for i in range(self.orbit_capacity)
                for role, sort in (
                    ("0-domain", CARRY_ACTION),
                    ("1-f5", F5),
                    ("2-epsilon", BOOL),
                )
            ),
        )
        self.zero = self.constant(BOOL, 0)
        self.one = self.constant(BOOL, 1)
        self.width = self.bits.variable((extent,), extent, self.width_sort)
        self.domains = tuple(
            self.bits.variable((p,), p, CARRY_ACTION) for p in self.ports[1::3]
        )
        self.values = tuple(
            ResidueMorphism(
                self.bits.variable((a,), a, F5), self.bits.variable((e,), e, BOOL)
            )
            for a, e in zip(self.ports[2::3], self.ports[3::3], strict=True)
        )
        self.kappa_precompositions = 0

    def _logical_inputs(
        self, width_is: tuple[FactoredFunctionID, ...]
    ) -> tuple[tuple[FactoredFunctionID, ...], tuple[ResidueMorphism, ...]]:
        if not self.symmetric:
            return self.domains, self.values
        b = self.bits
        zero_domain = self.constant(CARRY_ACTION, 0)
        blank = self.cocycles.constant(0, 0)
        domains: list[FactoredFunctionID] = []
        values: list[ResidueMorphism] = []
        for i in range(self.capacity):
            domain = zero_domain
            value = blank
            for m, condition in enumerate(width_is, 1):
                if i >= m:
                    continue
                orbit = min(i, m - 1 - i)
                domain = b.select(condition, self.domains[orbit], domain)
                value = ResidueMorphism(
                    b.select(condition, self.values[orbit].alpha, value.alpha),
                    b.select(condition, self.values[orbit].epsilon, value.epsilon),
                )
            domains.append(domain)
            values.append(value)
        return tuple(domains), tuple(values)

    def constant(self, sort: AtomSort, value: int) -> FactoredFunctionID:
        return self.bits.constant(FunctionSignature((), sort), value)

    def conjunction(
        self, left: FactoredFunctionID, right: FactoredFunctionID
    ) -> FactoredFunctionID:
        return self.bits.select(left, right, self.zero)

    def negate(self, value: FactoredFunctionID) -> FactoredFunctionID:
        return self.bits.map_atoms(value, BOOL, (1, 0))

    def width_at_most(self, value: int) -> FactoredFunctionID:
        if value < 0:
            return self.zero
        if value >= self.capacity:
            return self.bits.domain_predicate(self.width)
        # Finite addition is defined exactly when width <= value. Reuse that
        # owner's bounded comparator; no large unary width table is expanded.
        shifted = self.bits.add(
            self.width,
            self.constant(self.width_sort, self.capacity - value),
            self.width_sort,
        )
        return self.bits.domain_predicate(shifted)

    def pair(
        self, left: ResidueMorphism, right: ResidueMorphism
    ) -> tuple[ResidueMorphism, ThresholdCocycleResidualID]:
        self.kappa_precompositions += 1
        return self.cocycles.add(left, right), self.cocycles.precompose(
            self.cocycles.primitive, left, right
        )

    def compile_primitive(self) -> CocycleAction:
        b, k = self.bits, self.cocycles
        at_most = tuple(self.width_at_most(i) for i in range(self.capacity + 1))
        width_is = tuple(
            self.conjunction(at_most[i], self.negate(at_most[i - 1]))
            for i in range(1, self.capacity + 1)
        )
        admissible = self.negate(at_most[0])
        domains, values = self._logical_inputs(width_is)
        for i, (domain, value) in enumerate(
            zip(self.domains, self.values, strict=True)
        ):
            eq_domain = b.map_atoms(domain, BOOL, (0, 1, 0))
            eq_value = k.equal_nine(value)
            valid = self.negate(b.add(eq_domain, eq_value, BOOL, wrap=True))
            zero_domain = b.map_atoms(domain, BOOL, (1, 0, 0))
            zero_alpha = b.map_atoms(value.alpha, BOOL, (1, 0, 0, 0, 0))
            padding = self.conjunction(
                zero_domain,
                self.conjunction(zero_alpha, self.negate(value.epsilon)),
            )
            inactive = at_most[2 * i if self.symmetric else i]
            admissible = self.conjunction(
                admissible, b.select(inactive, padding, valid)
            )
            if self.symmetric:
                # Orbit i is the self-reflected center at width 2*i+1, so
                # its pair coefficient must have even parity.
                center = width_is[2 * i]
                admissible = self.conjunction(
                    admissible,
                    b.select(center, self.negate(value.epsilon), self.one),
                )
        carry = [self.zero]
        for domain in domains:
            carry.append(k.output.carry_apply(domain, carry[-1]))
        growth = self.zero
        for m, condition in enumerate(width_is, 1):
            growth = b.select(condition, carry[m], growth)
        next_width = b.add(self.width, growth, self.width_sort)
        admissible = self.conjunction(admissible, b.domain_predicate(next_width))
        normal = tuple(k.normalize(v, c) for v, c in zip(values, carry, strict=False))
        blank = k.constant(0, 0)
        edge = k.constant(1, 1)
        zero_k = k.intern(self.zero)
        output_capacity = self.orbit_capacity if self.symmetric else self.capacity
        output_values = [blank] * output_capacity
        output_k = [zero_k] * output_capacity
        for m, condition in enumerate(width_is, 1):
            limit = min(m + 1, output_capacity)
            if self.symmetric:
                limit = min((m + 2) // 2, output_capacity)
            for i in range(limit):
                low_live = not self.symmetric or i < (m + 1) // 2
                if i < m and low_live:
                    low, low_k = self.pair(normal[i], normal[m - 1 - i])
                else:
                    low, low_k = blank, zero_k
                if m < self.capacity:
                    # Growth reflects the extended normalized word. It is
                    # not forward adjacency of independently carried digits.
                    left = edge if i == m else normal[i]
                    right = edge if m - i == m else normal[m - i]
                    high, high_k = self.pair(left, right)
                    value = ResidueMorphism(
                        b.select(carry[m], high.alpha, low.alpha),
                        b.select(carry[m], high.epsilon, low.epsilon),
                    )
                    cocycle = k.intern(
                        b.select(carry[m], k.resolve(high_k), k.resolve(low_k))
                    )
                else:
                    # The growth branch at capacity is already undefined.
                    value, cocycle = low, low_k
                output_values[i] = ResidueMorphism(
                    b.select(condition, value.alpha, output_values[i].alpha),
                    b.select(condition, value.epsilon, output_values[i].epsilon),
                )
                output_k[i] = k.intern(
                    b.select(condition, k.resolve(cocycle), k.resolve(output_k[i]))
                )
        outputs = (
            next_width,
            *(
                f
                for value, cocycle in zip(output_values, output_k, strict=True)
                for f in (k.domain(value, cocycle), value.alpha, value.epsilon)
            ),
        )
        return self.temporal.primitive(self.ports, outputs, tuple(output_k), admissible)

    def binding(self, field: tuple[int, ...]) -> dict[PortVariable, int]:
        if not 1 <= len(field) <= self.capacity:
            raise ValueError("source does not fit the declared complete context")
        if self.symmetric and field != field[::-1]:
            raise ValueError("symmetric context requires a reflected pair field")
        source = field
        if self.symmetric:
            source = field[: (len(field) + 1) // 2]
            if len(field) % 2 and decimal_cocycle_coordinates(source[-1])[2] != 0:
                raise ValueError("odd symmetric center requires even parity")
        values = [len(field)]
        for s in source + (0,) * (self.orbit_capacity - len(source)):
            domain, alpha, epsilon = decimal_cocycle_coordinates(s)
            values.extend((DOMAINS.index(domain), alpha, epsilon))
        return dict(zip((p.variable for p in self.ports), values, strict=True))
