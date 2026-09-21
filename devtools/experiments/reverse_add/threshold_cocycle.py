"""Research-only decimal carry cocycles on supplied finite contexts.

This bounded reference is not a source-cylinder constructor or an installed
production execution owner. Its callers must supply complete finite contexts.

The semantic-function owner performs every reduction and substitution. A
residual's identity includes definedness and its declared context, but never
the affine expressions or source values from which the function was built.
EQ remains a separate predicate on the additive value result.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_pair_carry_action,
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
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.reverse_add.active_output import (
    CARRY_ACTION,
    DIGIT,
    F5,
    ReverseActiveOutputArena,
)


@dataclass(frozen=True, slots=True)
class ResidueMorphism:
    """Separate additive F5 and F2 outputs; epsilon is decimal parity."""

    alpha: FactoredFunctionID
    epsilon: FactoredFunctionID


@dataclass(frozen=True, slots=True)
class ThresholdCocycleResidualID:
    """A canonical Boolean function, including the admitted domain."""

    function: FactoredFunctionID


class ThresholdCocycleArena:
    def __init__(self, bits: BitFunctionArena) -> None:
        if type(bits) is not BitFunctionArena:
            raise TypeError("cocycles require an owned finite-function arena")
        self.bits = bits
        self._owner = bits.ledger.register(
            f"threshold-cocycle-roots-{len(bits.ledger.inventory())}",
            "semantic_cocycle_roots",
        )
        self._residuals: LedgerDict[FactoredFunctionID, bool] = bits.ledger.make_dict(
            self._owner
        )
        bits.ledger.register_execution_root(self)
        bits.ledger.register_container(
            self._owner,
            self._residuals,
            node_count=lambda: len(self._residuals),
            payloads=self._residuals.items,
        )
        self.output = ReverseActiveOutputArena(bits)
        self.ports = tuple(
            FinitePort(PortVariable(0, i, "decimal-cocycle-argument", 0), 10)
            for i in range(2)
        )
        x, y = (bits.variable(self.ports, p, DIGIT) for p in self.ports)
        total = bits.add(x, y, AtomSort("decimal-cocycle-sum", 19))
        self.primitive = self.intern(
            bits.map_atoms(
                total,
                BOOL,
                tuple(
                    int(decimal_pair_carry_action(v) is CarryFn.CONST1)
                    for v in range(19)
                ),
            )
        )

    def _sort(self, function: FactoredFunctionID, expected: AtomSort) -> None:
        if self.bits.resolve(function).signature.output != expected:
            raise ValueError("cocycle function has another output sort")

    def intern(self, function: FactoredFunctionID) -> ThresholdCocycleResidualID:
        self._sort(function, BOOL)
        if function not in self._residuals:
            self.bits.ledger.reserve(self._owner, entries=1, nodes=1)
            self._residuals[function] = True
        return ThresholdCocycleResidualID(function)

    @property
    def residual_count(self) -> int:
        return len(self._residuals)

    def resolve(self, residual: ThresholdCocycleResidualID) -> FactoredFunctionID:
        if type(residual) is not ThresholdCocycleResidualID:
            raise TypeError("expected a threshold cocycle residual")
        self._sort(residual.function, BOOL)
        if residual.function not in self._residuals:
            raise ValueError("cocycle residual was not interned in this arena")
        return residual.function

    def constant(self, alpha: int, epsilon: int) -> ResidueMorphism:
        return ResidueMorphism(
            self.bits.constant(FunctionSignature((), F5), alpha),
            self.bits.constant(FunctionSignature((), BOOL), epsilon),
        )

    def representative(self, value: ResidueMorphism) -> FactoredFunctionID:
        """A bounded local CRT representative, never a decimal value field."""
        self._sort(value.alpha, F5)
        self._sort(value.epsilon, BOOL)
        parity = self.bits.map_atoms(value.alpha, BOOL, (0, 1, 0, 1, 0))
        beta = self.bits.add(parity, value.epsilon, BOOL, wrap=True)
        high = self.bits.map_atoms(beta, AtomSort("decimal-five", 6), (0, 5))
        return self.bits.add(value.alpha, high, DIGIT)

    def from_representative(self, value: FactoredFunctionID) -> ResidueMorphism:
        self._sort(value, DIGIT)
        return ResidueMorphism(
            self.bits.map_atoms(value, F5, tuple(v % 5 for v in range(10))),
            self.bits.map_atoms(value, BOOL, tuple(v % 2 for v in range(10))),
        )

    def add(self, left: ResidueMorphism, right: ResidueMorphism) -> ResidueMorphism:
        self._sort(left.epsilon, BOOL)
        self._sort(right.epsilon, BOOL)
        return ResidueMorphism(
            self.output.add_alpha(left.alpha, right.alpha),
            self.bits.add(left.epsilon, right.epsilon, BOOL, wrap=True),
        )

    def normalize(
        self, value: ResidueMorphism, carry: FactoredFunctionID
    ) -> ResidueMorphism:
        self._sort(carry, BOOL)
        lifted = self.bits.map_atoms(carry, F5, (0, 1))
        return self.add(value, ResidueMorphism(lifted, carry))

    def equal_nine(self, value: ResidueMorphism) -> FactoredFunctionID:
        self._sort(value.alpha, F5)
        self._sort(value.epsilon, BOOL)
        four = self.bits.map_atoms(value.alpha, BOOL, (0, 0, 0, 0, 1))
        zero = self.bits.constant(FunctionSignature((), BOOL), 0)
        return self.bits.select(four, value.epsilon, zero)

    def precompose(
        self,
        residual: ThresholdCocycleResidualID,
        left: ResidueMorphism,
        right: ResidueMorphism,
    ) -> ThresholdCocycleResidualID:
        function = self.resolve(residual)
        return self.intern(
            self.bits.substitute(
                function,
                {
                    self.ports[0].variable: self.representative(left),
                    self.ports[1].variable: self.representative(right),
                },
            )
        )

    def restrict(
        self,
        residual: ThresholdCocycleResidualID,
        admissible: FactoredFunctionID,
    ) -> ThresholdCocycleResidualID:
        return self.intern(self.bits.restrict(self.resolve(residual), admissible))

    def compose_temporal(
        self,
        after: ThresholdCocycleResidualID,
        transport: Mapping[PortVariable, FactoredFunctionID],
        before: ThresholdCocycleResidualID,
    ) -> ThresholdCocycleResidualID:
        """Pull back the next cocycle and retain the earlier legal context.

        The caller supplies every changed boundary/value port, including the
        previous domain output. This operation does not discover missing ports
        or assert that a caller's context is closed under arithmetic growth.
        """
        following = self.resolve(after)
        preceding = self.resolve(before)
        expected = {p.variable for p in self.bits.resolve(following).signature.inputs}
        if set(transport) != expected:
            raise ValueError("temporal pullback must replace every after-context port")
        context = set(self.bits.resolve(preceding).signature.inputs)
        for value in transport.values():
            if not set(self.bits.resolve(value).signature.inputs) <= context:
                raise ValueError("temporal transport introduces an unadmitted context")
        pulled = self.bits.substitute(following, transport)
        allowed = self.bits.domain_predicate(preceding)
        return self.intern(self.bits.restrict(pulled, allowed))

    def domain(
        self,
        value: ResidueMorphism,
        cocycle: ThresholdCocycleResidualID,
    ) -> FactoredFunctionID:
        """GT from kappa; otherwise EQ from the additive residue being nine."""
        kappa = self.resolve(cocycle)
        context = set(self.bits.resolve(value.alpha).signature.inputs) | set(
            self.bits.resolve(value.epsilon).signature.inputs
        )
        if context != set(self.bits.resolve(kappa).signature.inputs):
            raise ValueError("cocycle and value require the same declared context")
        eq = self.equal_nine(value)
        low = self.bits.map_atoms(eq, CARRY_ACTION, (0, 1))
        high = self.bits.constant(FunctionSignature((), CARRY_ACTION), 2)
        # Sum of two decimal representatives cannot be nineteen. Reject an
        # inconsistent externally supplied kappa/value pair as undefined.
        not_eq = self.bits.map_atoms(eq, BOOL, (1, 0))
        one = self.bits.constant(FunctionSignature((), BOOL), 1)
        valid = self.bits.select(kappa, not_eq, one)
        return self.bits.restrict(self.bits.select(kappa, high, low), valid)

    def nodes(self, residual: ThresholdCocycleResidualID) -> int:
        node = self.bits.resolve(self.resolve(residual))
        return len(
            {
                n
                for root in (*node.bits, node.valid)
                for n in self.bits.functions.iter_reachable(root)
            }
        )
