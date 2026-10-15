"""Executable local output/control morphisms on bounded coordinate ports.

An input port denotes a value at a caller-declared relative coordinate or cut.
The same function applies at every translated coordinate. Keys contain reduced
output functions only: no source, width, temporal recipe, or transport/birth
decomposition. These local arrows do NOT certify a whole active future class.
Spatial carry geometry and a closed consumer profile must still be supplied.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_normalized_coordinates,
    decimal_pair_carry_action,
    decimal_pair_coordinates,
    decimal_q95,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.polynomials.centered_f5 import CenteredF5Transport
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.stores import LedgerDict, LedgerList, append_indexed_node

PAIR = AtomSort("reverse-decimal-pair", 19)
F5 = AtomSort("reverse-F5", 5)
DIGIT = AtomSort("reverse-decimal-digit", 10)
CARRY_ACTION = AtomSort("reverse-carry-action", 3)
Q95 = AtomSort("reverse-Q95", 95)
_CARRIES = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)


class ReverseActiveOutputArena:
    """Intern exact local output functions after cancellation and composition.

    This owner is intentionally separate from source-independent temporal
    programs and from certified quiescent FutureBehaviorClassID publication.
    Function signatures and invalid-domain predicates are part of equality.
    """

    _KIND = "coordinate-output-morphism"

    def __init__(self, bits: BitFunctionArena) -> None:
        if type(bits) is not BitFunctionArena:
            raise TypeError("active output requires an owned finite-function arena")
        self.bits = bits
        self.ledger: ResourceLedger = bits.ledger
        self.owner = ArenaToken("reverse-active-output")
        self.ledger.register_execution_root(self)
        prefix = f"reverse-active-output-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "reverse_active_output"
        )
        self._key_owner = self.ledger.register(
            prefix + "-keys", "reverse_active_output_interner"
        )
        self._nodes: LedgerList[FactoredFunctionID] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: LedgerDict[FactoredFunctionID, int] = self.ledger.make_dict(
            self._key_owner
        )
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        self.ledger.register_container(
            self._key_owner, self._keys, payloads=self._keys.items
        )

    def _domain(self, function: FactoredFunctionID, expected: AtomSort) -> None:
        if self.bits.resolve(function).signature.output != expected:
            raise ValueError("reverse output function has another channel sort")

    def resolve(self, output: CoordinateOutputMorphismID) -> FactoredFunctionID:
        if type(output) is not CoordinateOutputMorphismID:
            raise TypeError("expected an active coordinate output ID")
        output.validate(self.owner, self._KIND, size=len(self._nodes))
        function = self._nodes[output.local_id]
        self._domain(function, PAIR)
        return function

    def intern(self, function: FactoredFunctionID) -> CoordinateOutputMorphismID:
        self._domain(function, PAIR)
        self.ledger.bump(_reverse_add_keys.REVERSE_ACTIVE_OUTPUT_REQUESTS)
        found = self._keys.get(function)
        if found is not None:
            self.ledger.bump(_reverse_add_keys.REVERSE_ACTIVE_OUTPUT_HITS)
            return CoordinateOutputMorphismID(self.owner, self._KIND, found)
        local_id = append_indexed_node(
            self.ledger,
            self._nodes,
            self._keys,
            self._node_owner,
            self._key_owner,
            function,
            function,
        )
        self.ledger.bump(_reverse_add_keys.REVERSE_ACTIVE_OUTPUT_PUBLICATIONS)
        return CoordinateOutputMorphismID(self.owner, self._KIND, local_id)

    def normalized(
        self, symbol: FactoredFunctionID, carry: FactoredFunctionID
    ) -> FactoredFunctionID:
        self._domain(symbol, PAIR)
        self._domain(carry, BOOL)
        digits = tuple(
            a + 5 * b
            for a, b in (decimal_normalized_coordinates(s, 0) for s in range(19))
        )
        digit = self.bits.map_atoms(symbol, DIGIT, digits)
        total = self.bits.add(digit, carry, AtomSort("reverse-carried-digit", 11))
        return self.bits.map_atoms(total, DIGIT, tuple(s % 10 for s in range(11)))

    def pair(
        self,
        left: FactoredFunctionID,
        left_carry: FactoredFunctionID,
        right: FactoredFunctionID,
        right_carry: FactoredFunctionID,
    ) -> CoordinateOutputMorphismID:
        """Compose normalization and pairing without constructing an output tile."""
        return self.intern(
            self.bits.add(
                self.normalized(left, left_carry),
                self.normalized(right, right_carry),
                PAIR,
            )
        )

    def coordinates(
        self, output: CoordinateOutputMorphismID
    ) -> tuple[FactoredFunctionID, FactoredFunctionID, FactoredFunctionID]:
        function = self.resolve(output)
        coordinates = tuple(decimal_pair_coordinates(s) for s in range(19))
        return (
            self.bits.map_atoms(function, F5, tuple(c[0] for c in coordinates)),
            self.bits.map_atoms(function, BOOL, tuple(c[1] for c in coordinates)),
            self.bits.map_atoms(function, BOOL, tuple(c[2] for c in coordinates)),
        )

    def from_coordinates(
        self,
        alpha: FactoredFunctionID,
        beta: FactoredFunctionID,
        nu: FactoredFunctionID,
    ) -> CoordinateOutputMorphismID:
        """Combine all channels before interning; (4,1,1) stays undefined."""
        self._domain(alpha, F5)
        self._domain(beta, BOOL)
        self._domain(nu, BOOL)
        high_digit = self.bits.map_atoms(beta, AtomSort("reverse-five-bit", 6), (0, 5))
        high_pair = self.bits.map_atoms(nu, AtomSort("reverse-ten-bit", 11), (0, 10))
        digit = self.bits.add(alpha, high_digit, DIGIT)
        return self.intern(self.bits.add(digit, high_pair, PAIR))

    def add_alpha(
        self, first: FactoredFunctionID, second: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Reduce the combined F5 function, forgetting the summand provenance."""
        self._domain(first, F5)
        self._domain(second, F5)
        total = self.bits.add(first, second, AtomSort("reverse-F5-sum", 9))
        return self.bits.map_atoms(total, F5, tuple(s % 5 for s in range(9)))

    def transported_alpha(
        self,
        transport: CenteredF5Transport,
        sample: Callable[[int], FactoredFunctionID],
        birth: FactoredFunctionID,
        *,
        max_terms: int = 4096,
    ) -> FactoredFunctionID:
        """Apply centered shifts and immediately combine with the birth function.

        The callback binds relative-coordinate ports and is never retained.
        A dense operator is rejected before the first source callback.
        """
        if type(transport) is not CenteredF5Transport:
            raise TypeError("F5 transport requires a centered operator")
        self._domain(birth, F5)
        shifts = transport.shifts(max_terms=max_terms)
        result = birth
        for offset, coefficient in shifts:
            source = sample(offset)
            self._domain(source, F5)
            scaled = self.bits.map_atoms(
                source, F5, tuple(coefficient * s % 5 for s in range(5))
            )
            result = self.add_alpha(result, scaled)
        return result

    def carry_action(self, output: CoordinateOutputMorphismID) -> FactoredFunctionID:
        return self.bits.map_atoms(
            self.resolve(output),
            CARRY_ACTION,
            tuple(_CARRIES.index(decimal_pair_carry_action(s)) for s in range(19)),
        )

    def q95(
        self, output: CoordinateOutputMorphismID, forcing: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Publish the fixed local carrier, without primitive boundary ports."""
        self._domain(forcing, F5)
        carrier = self.bits.map_atoms(
            self.resolve(output), Q95, tuple(decimal_q95(s, 0) for s in range(19))
        )
        return self.bits.add(carrier, forcing, Q95)

    def q95_output(self, carrier: FactoredFunctionID) -> CoordinateOutputMorphismID:
        self._domain(carrier, Q95)
        output, _forcing = self.bits.divmod_atoms(carrier, 5, PAIR, F5)
        return self.intern(output)

    def q95_forcing(self, carrier: FactoredFunctionID) -> FactoredFunctionID:
        self._domain(carrier, Q95)
        _output, forcing = self.bits.divmod_atoms(carrier, 5, PAIR, F5)
        return forcing

    def q95_carry(self, carrier: FactoredFunctionID) -> FactoredFunctionID:
        """Project K0/identity/K1 from Q95, without interning output S.

        The output symbol is ``q // 5``.  Its carry domain is a derived view,
        so this projection must not publish another output function as state.
        Incoming physical carry remains a later monoid consumer.
        """
        self._domain(carrier, Q95)
        symbol, _forcing = self.bits.divmod_atoms(carrier, 5, PAIR, F5)
        return self.bits.map_atoms(
            symbol,
            CARRY_ACTION,
            tuple(_CARRIES.index(decimal_pair_carry_action(s)) for s in range(19)),
        )

    def carry_then(
        self, before: FactoredFunctionID, after: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Spatial carry composition: after o before, with no reflected scan."""
        self._domain(before, CARRY_ACTION)
        self._domain(after, CARRY_ACTION)
        identity = self.bits.map_atoms(after, BOOL, (0, 1, 0))
        return self.bits.select(identity, before, after)

    def carry_apply(
        self, action: FactoredFunctionID, incoming: FactoredFunctionID
    ) -> FactoredFunctionID:
        self._domain(action, CARRY_ACTION)
        self._domain(incoming, BOOL)
        identity = self.bits.map_atoms(action, BOOL, (0, 1, 0))
        reset = self.bits.map_atoms(action, BOOL, (0, 0, 1))
        return self.bits.select(identity, incoming, reset)

    def substitute(
        self,
        output: CoordinateOutputMorphismID,
        replacements: Mapping[PortVariable, FactoredFunctionID],
    ) -> CoordinateOutputMorphismID:
        return self.intern(self.bits.substitute(self.resolve(output), replacements))

    def constant(self, symbol: int) -> CoordinateOutputMorphismID:
        return self.intern(self.bits.constant(FunctionSignature((), PAIR), symbol))
