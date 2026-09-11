"""Factored finite numeric outputs without atom-domain truth enumeration.

A value is a fixed tuple of canonical Boolean functions plus one admissibility
predicate. Invalid assignments have all bits canonically zero. Division is a
bounded comparator/subtractor circuit, never a table with one row per radix.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticRequest,
    SemanticTerminal,
    _ports,
    _signature,
    _union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.boolean_composition import (
    _CompositionKey,
    substitute_boolean_fused,
)
from number_compiler.hashlife.interfaces.semantic_publication import prepare_functions
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class FactoredFunctionID(ArenaHandle):
    """Canonical fixed-bit finite output in one semantic arena."""


@dataclass(frozen=True, slots=True)
class FactoredFunction:
    signature: FunctionSignature
    bits: tuple[SemanticFunctionID, ...]
    valid: SemanticFunctionID


@dataclass(frozen=True, slots=True)
class BinaryDivision:
    remainder: FactoredFunctionID
    quotient: FactoredFunctionID


@dataclass(frozen=True, slots=True)
class BitSubstitutionKey:
    function: FactoredFunctionID
    replacements: tuple[tuple[PortVariable, FactoredFunctionID], ...]


@dataclass(frozen=True, slots=True)
class _PendingFunction:
    signature: FunctionSignature
    bits: tuple[int, ...]
    valid: int


class BitFunctionArena:
    """Finite arithmetic semantics sharing one ledger-owned Boolean DAG."""

    def __init__(
        self, ledger: ResourceLedger, functions: SemanticFunctionArena | None = None
    ) -> None:
        if functions is not None and (
            type(functions) is not SemanticFunctionArena
            or functions.ledger is not ledger
        ):
            raise ValueError("factored functions require the same semantic ledger")
        self.ledger = ledger
        self.functions = (
            SemanticFunctionArena(ledger) if functions is None else functions
        )
        self.token = ArenaToken("semantic-bits")
        ledger.register_execution_root(self)
        prefix = f"semantic-bits-{len(ledger.inventory())}"
        self.node_owner = ledger.register(
            prefix + "-nodes", "semantic_factored_function"
        )
        self.key_owner = ledger.register(prefix + "-keys", "semantic_factored_interner")
        self.nodes: LedgerList[FactoredFunction] = ledger.make_list(self.node_owner)
        self.keys: LedgerDict[FactoredFunction, int] = ledger.make_dict(self.key_owner)
        scalar_owner = ledger.register(prefix + "-scalar-sources", "query_memo")
        self._scalar_sources: OwnedMemo[SemanticFunctionID, FactoredFunctionID] = (
            OwnedMemo(ledger, scalar_owner, evictable=True)
        )
        substitution_owner = ledger.register(prefix + "-substitutions", "query_memo")
        self._compositions: OwnedMemo[BitSubstitutionKey, FactoredFunctionID] = (
            OwnedMemo(
                ledger, substitution_owner, evictable=True, composition_entries=True
            )
        )

    def _handle(self, identity: int) -> FactoredFunctionID:
        return FactoredFunctionID(self.token, "semantic-bit-function", identity)

    def resolve(self, function: FactoredFunctionID) -> FactoredFunction:
        if type(function) is not FactoredFunctionID:
            raise ValueError("factored function requires a scoped identity")
        ArenaHandle.validate(
            function, self.token, "semantic-bit-function", size=len(self.nodes)
        )
        return self.nodes[function.local_id]

    def from_scalar(self, function: SemanticFunctionID) -> FactoredFunctionID:
        """Reuse the complete scalar-to-bit conversion before touching its DAG."""
        node = self.functions.resolve(function)
        _signature(node.signature)
        if type(node.signature.output) is not AtomSort:
            raise ValueError("factored conversion requires a scalar semantic output")
        self.ledger.bump("semantic_bit_from_scalar_requests")
        cached = self._scalar_sources.get(function)
        if cached is not None:
            self.resolve(cached)
            self.ledger.bump("semantic_bit_from_scalar_hits")
            return cached
        # Every new association needs one entry even if its canonical function
        # already exists. Reject a full budget before traversing primitive data.
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            from number_compiler.arithmetic.contracts.block_effect import (
                BlockContextBudgetExceeded,
            )

            raise BlockContextBudgetExceeded(
                "scalar conversion cache budget exhausted before construction"
            )
        circuit = _Circuit(self.functions, node.signature.inputs)
        tx = circuit.tx
        width = (node.signature.output.cardinality - 1).bit_length()
        pending = [(function.local_id, False)]
        done: dict[int, tuple[int, ...]] = {}
        while pending:
            identity, ready = pending.pop()
            self.ledger.bump("semantic_bit_from_scalar_frames")
            if identity in done:
                continue
            current = tx.node(identity)
            leaf = current.terminal
            if leaf is not None:
                values = tuple(
                    circuit.one
                    if leaf.kind == "atom" and (leaf.value >> bit) & 1
                    else circuit.zero
                    for bit in range(width)
                )
                done[identity] = (
                    *values,
                    circuit.one if leaf.kind == "atom" else circuit.zero,
                )
            elif ready:
                assert current.variable is not None
                done[identity] = tuple(
                    tx.rebuilt_decision(circuit.signature, current.variable, low, high)
                    for low, high in zip(
                        done[current.low], done[current.high], strict=True
                    )
                )
            else:
                pending.extend(
                    ((identity, True), (current.high, False), (current.low, False))
                )
        roots = done[function.local_id]
        result = circuit.normalized(node.signature, roots[:-1], roots[-1])
        self.ledger.bump("semantic_bit_from_scalar_evaluations")
        return self._publish(circuit, (result,), scalar_source=function)[0]

    def variable(
        self,
        inputs: tuple[FinitePort, ...],
        port: FinitePort,
        output: AtomSort | None = None,
    ) -> FactoredFunctionID:
        _ports(inputs)
        _ports((port,))
        if port not in inputs:
            raise ValueError("factored variable is not a declared port")
        target = (
            AtomSort(port.variable.role, port.cardinality) if output is None else output
        )
        signature = FunctionSignature(inputs, target)
        if type(target) is not AtomSort or target.cardinality != port.cardinality:
            raise ValueError("factored input/output domains disagree")
        circuit = _Circuit(self.functions, inputs)
        bits = tuple(
            circuit.tx.bit(
                inputs,
                PortVariable(
                    port.variable.time, port.variable.side, port.variable.role, bit
                ),
            )
            for bit in range(port.bits)
        )
        value = circuit.normalized(signature, bits, circuit.admitted())
        return self._publish(circuit, (value,))[0]

    def constant(self, signature: FunctionSignature, value: int) -> FactoredFunctionID:
        _signature(signature)
        target = signature.output
        if (
            type(target) is not AtomSort
            or type(value) is not int
            or not 0 <= value < target.cardinality
        ):
            raise ValueError("factored constant must fit a bounded atom sort")
        circuit = _Circuit(self.functions, signature.inputs)
        bits = tuple(
            circuit.one if (value >> bit) & 1 else circuit.zero
            for bit in range((target.cardinality - 1).bit_length())
        )
        result = circuit.normalized(signature, bits, circuit.admitted())
        return self._publish(circuit, (result,))[0]

    def add(
        self,
        first: FactoredFunctionID,
        second: FactoredFunctionID,
        output: AtomSort,
        *,
        wrap: bool = False,
    ) -> FactoredFunctionID:
        """Exact finite addition; optional wrapping requires a power-of-two sort."""
        a, b = self.resolve(first), self.resolve(second)
        if type(wrap) is not bool:
            raise TypeError("addition wrapping must be a boolean")
        inputs = _union_inputs(a.signature.inputs, b.signature.inputs)
        signature = FunctionSignature(inputs, output)
        if type(output) is not AtomSort:
            raise ValueError("numeric addition needs an atom output")
        width = (output.cardinality - 1).bit_length()
        if wrap and output.cardinality != 1 << width:
            raise ValueError("wrapping addition requires a power-of-two output sort")
        circuit = _Circuit(self.functions, inputs)
        aa, av = circuit.imported(a)
        bb, bv = circuit.imported(b)
        carry = circuit.zero
        bits = []
        for bit in range(width):
            left = aa[bit] if bit < len(aa) else circuit.zero
            right = bb[bit] if bit < len(bb) else circuit.zero
            parity = circuit.xor(left, right)
            bits.append(circuit.xor(parity, carry))
            carry = circuit.choose(parity, carry, left)
        valid = circuit.conjunction(av, bv)
        if not wrap:
            overflow = carry
            for high in aa[width:] + bb[width:]:
                overflow = circuit.choose(high, circuit.one, overflow)
            valid = circuit.conjunction(valid, circuit.negate(overflow))
        if output.cardinality != 1 << width:
            _, borrow = circuit.subtract_constant(tuple(bits), output.cardinality)
            valid = circuit.conjunction(valid, borrow)
        result = circuit.normalized(signature, tuple(bits), valid)
        return self._publish(circuit, (result,))[0]

    def select(
        self,
        condition: FactoredFunctionID,
        yes: FactoredFunctionID,
        no: FactoredFunctionID,
    ) -> FactoredFunctionID:
        c, a, b = (self.resolve(item) for item in (condition, yes, no))
        if (
            type(c.signature.output) is not AtomSort
            or c.signature.output.cardinality != 2
            or a.signature.output != b.signature.output
        ):
            raise ValueError(
                "factored select requires a bit and identical result sorts"
            )
        inputs = _union_inputs(
            c.signature.inputs, a.signature.inputs, b.signature.inputs
        )
        circuit = _Circuit(self.functions, inputs)
        cc, cv = circuit.imported(c)
        aa, av = circuit.imported(a)
        bb, bv = circuit.imported(b)
        valid = circuit.conjunction(cv, circuit.choose(cc[0], av, bv))
        valid = circuit.conjunction(circuit.admitted(), valid)
        bits = tuple(circuit.choose(cc[0], left, right) for left, right in zip(aa, bb))
        signature = FunctionSignature(inputs, a.signature.output)
        result = circuit.normalized(signature, bits, valid)
        return self._publish(circuit, (result,))[0]

    def map_atoms(
        self,
        function: FactoredFunctionID,
        output: AtomSort,
        table: tuple[int, ...],
    ) -> FactoredFunctionID:
        """Compose a bounded unary law with a factored function.

        Only the primitive alphabet (at most 64 atoms) is inspected. The
        function's input ports are never expanded into a Cartesian table.
        Invalid inputs remain invalid, including when the map is constant.
        """
        source = self.resolve(function)
        domain = source.signature.output
        signature = FunctionSignature(source.signature.inputs, output)
        if (
            type(domain) is not AtomSort
            or type(output) is not AtomSort
            or domain.cardinality > 64
            or type(table) is not tuple
            or len(table) != domain.cardinality
            or any(type(v) is not int or not 0 <= v < output.cardinality for v in table)
        ):
            raise ValueError("unary atom map requires a complete bounded finite law")
        circuit = _Circuit(self.functions, source.signature.inputs)
        source_bits, valid = circuit.imported(source)
        width = (output.cardinality - 1).bit_length()
        values = [
            tuple(
                circuit.one if answer & (1 << bit) else circuit.zero
                for bit in range(width)
            )
            for answer in table + (0,) * ((1 << len(source_bits)) - len(table))
        ]
        # Shannon-compose one bounded unary table. Pairing adjacent codes
        # eliminates the low input bit first; no joint port table is built.
        for condition in source_bits:
            values = [
                tuple(
                    circuit.choose(condition, high, low)
                    for low, high in zip(values[i], values[i + 1], strict=True)
                )
                for i in range(0, len(values), 2)
            ]
        result = circuit.normalized(signature, values[0], valid)
        return self._publish(circuit, (result,))[0]

    def restrict(
        self, function: FactoredFunctionID, predicate: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Restrict a function's domain, retaining admissibility in its identity."""
        value, guard = self.resolve(function), self.resolve(predicate)
        if guard.signature.output != BOOL:
            raise ValueError("function restriction requires a Boolean predicate")
        inputs = _union_inputs(value.signature.inputs, guard.signature.inputs)
        circuit = _Circuit(self.functions, inputs)
        bits, valid = circuit.imported(value)
        condition, admitted = circuit.imported(guard)
        valid = circuit.conjunction(valid, circuit.conjunction(admitted, condition[0]))
        result = circuit.normalized(
            FunctionSignature(inputs, value.signature.output), bits, valid
        )
        return self._publish(circuit, (result,))[0]

    def bundle(
        self, functions: tuple[FactoredFunctionID, ...], *, name: str
    ) -> FactoredFunctionID:
        """A bounded observation/context record, with shared validity and bits."""
        if type(functions) is not tuple or not 1 <= len(functions) <= 8:
            raise ValueError("a finite observation record requires one to eight fields")
        nodes = tuple(self.resolve(f) for f in functions)
        width = sum(len(n.bits) for n in nodes)
        if width > 64:
            raise ValueError("finite observation record exceeds one bounded word")
        inputs = _union_inputs(*(n.signature.inputs for n in nodes))
        layout = tuple(node.signature.output for node in nodes)
        signature = FunctionSignature(
            inputs, AtomSort(f"{name}:{layout!r}", 1 << width)
        )
        circuit = _Circuit(self.functions, inputs)
        bits: tuple[int, ...] = ()
        valid = circuit.one
        for node in nodes:
            component, admitted = circuit.imported(node)
            bits += component
            valid = circuit.conjunction(valid, admitted)
        return self._publish(circuit, (circuit.normalized(signature, bits, valid),))[0]

    def domain_predicate(self, function: FactoredFunctionID) -> FactoredFunctionID:
        """Return definedness as a Boolean function on the declared port domain."""
        node = self.resolve(function)
        circuit = _Circuit(self.functions, node.signature.inputs)
        _, valid = circuit.imported(node)
        signature = FunctionSignature(node.signature.inputs, BOOL)
        result = circuit.normalized(signature, (valid,), circuit.admitted())
        return self._publish(circuit, (result,))[0]

    def substitute(
        self,
        function: FactoredFunctionID,
        replacements: Mapping[PortVariable, FactoredFunctionID],
        *,
        joint: bool = True,
    ) -> FactoredFunctionID:
        """Simultaneously substitute finite numeric ports through Boolean bits."""
        if type(joint) is not bool:
            raise TypeError("substitution strategy requires a Boolean flag")
        original = self.resolve(function)
        admitted = {port.variable: port for port in original.signature.inputs}
        items = []
        references = []
        for variable, reference in replacements.items():
            if type(variable) is not PortVariable:
                raise ValueError("substitution needs typed finite port names")
            PortVariable.__post_init__(variable)
            port = admitted.get(variable)
            replacement = self.resolve(reference)
            if (
                port is None
                or type(replacement.signature.output) is not AtomSort
                or replacement.signature.output.cardinality != port.cardinality
            ):
                raise ValueError("substitution changes a finite input domain")
            items.append((port, replacement))
            references.append((variable, reference))
        items.sort(key=lambda item: item[0].variable)
        removed = {port.variable for port, _ in items}
        inputs = _union_inputs(
            tuple(
                port
                for port in original.signature.inputs
                if port.variable not in removed
            ),
            *(value.signature.inputs for _, value in items),
        )
        key = BitSubstitutionKey(function, tuple(sorted(references)))
        self.ledger.bump("semantic_bit_composition_requests")
        cached = self._compositions.get(key)
        if cached is not None:
            self.resolve(cached)
            self.ledger.bump("semantic_bit_composition_hits")
            return cached
        if not items:
            return function
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            from number_compiler.arithmetic.contracts.block_effect import (
                BlockContextBudgetExceeded,
            )

            raise BlockContextBudgetExceeded(
                "bit substitution cache budget exhausted before construction"
            )
        circuit = _Circuit(self.functions, inputs)
        mapping: dict[PortVariable, int] = {}
        validity = circuit.admitted()
        for port, value in items:
            bits, valid = circuit.imported(value)
            validity = circuit.conjunction(validity, valid)
            for bit, root in enumerate(bits):
                mapping[
                    PortVariable(
                        port.variable.time, port.variable.side, port.variable.role, bit
                    )
                ] = root
        # Cofactor correlated argument functions jointly; bottom-up ITE builds
        # functions for combinations of argument bits that can never coexist.
        fused = joint and any(
            len(circuit.tx.node(value).support) > 1 for value in mapping.values()
        )
        transform = substitute_boolean_fused if fused else substitute_boolean
        result_bits = tuple(
            transform(circuit, bit.local_id, mapping) for bit in original.bits
        )
        valid = transform(circuit, original.valid.local_id, mapping)
        result = circuit.normalized(
            FunctionSignature(inputs, original.signature.output),
            result_bits,
            circuit.conjunction(validity, valid),
        )
        self.ledger.bump("semantic_bit_composition_evaluations")
        return self._publish(circuit, (result,), substitution=key)[0]

    def divide_binary(
        self,
        radix: int,
        carry: FinitePort,
        symbol: FinitePort,
        inputs: tuple[FinitePort, ...] | None = None,
    ) -> BinaryDivision:
        """Complete q=(2c+b)//r, c'=(2c+b)%r for c<r and b<2."""
        if type(radix) is not int or not 1 <= radix <= 1 << 63:
            raise ValueError("division radix must be an integer in 1..2**63")
        _ports((carry,))
        _ports((symbol,))
        if (
            carry.variable == symbol.variable
            or carry.cardinality != radix
            or symbol.cardinality != 2
        ):
            raise ValueError("division requires distinct carry:r and symbol:2 ports")
        bundle = _union_inputs((carry,), (symbol,)) if inputs is None else inputs
        _ports(bundle)
        if carry not in bundle or symbol not in bundle:
            raise ValueError("division ports must be declared")
        circuit = _Circuit(self.functions, bundle)
        symbol_bit = circuit.tx.bit(bundle, symbol.variable)
        carry_bits = tuple(
            circuit.tx.bit(
                bundle,
                PortVariable(
                    carry.variable.time, carry.variable.side, carry.variable.role, bit
                ),
            )
            for bit in range(carry.bits)
        )
        doubled = (symbol_bit,) + carry_bits
        difference, borrow = circuit.subtract_constant(doubled, radix)
        quotient = circuit.negate(borrow)
        remainder = tuple(
            circuit.choose(quotient, difference[bit], doubled[bit])
            for bit in range(carry.bits)
        )
        valid = circuit.admitted()
        remain = circuit.normalized(
            FunctionSignature(bundle, AtomSort("division-carry", radix)),
            remainder,
            valid,
        )
        quot = circuit.normalized(FunctionSignature(bundle, BOOL), (quotient,), valid)
        result = self._publish(circuit, (remain, quot))
        self.ledger.bump("semantic_binary_division_compilations")
        return BinaryDivision(result[0], result[1])

    def evaluate(
        self, function: FactoredFunctionID, inputs: Mapping[PortVariable, int]
    ) -> int | None:
        node = self.resolve(function)
        # Shared evaluate validates every encoded integer before telemetry.
        valid = self.functions.evaluate(node.valid, inputs)
        if valid.kind != "atom":
            raise AssertionError("factored validity is not a total Boolean function")
        if not valid.value:
            return None
        value = 0
        for bit, function_bit in enumerate(node.bits):
            terminal = self.functions.evaluate(function_bit, inputs)
            if terminal.kind != "atom":
                raise AssertionError("factored bit is not a total Boolean function")
            shifted = self.ledger.observe_arithmetic(terminal.value << bit)
            value = self.ledger.observe_arithmetic(value | shifted)
        return value

    def _publish(
        self,
        circuit: _Circuit,
        results: tuple[_PendingFunction, ...],
        *,
        scalar_source: SemanticFunctionID | None = None,
        substitution: BitSubstitutionKey | None = None,
    ) -> tuple[FactoredFunctionID, ...]:
        if scalar_source is not None:
            source = self.functions.resolve(scalar_source)
            if len(results) != 1 or results[0].signature != source.signature:
                raise ValueError(
                    "scalar conversion publication requires one matching complete interface"
                )
        transaction = circuit.tx
        roots = tuple(
            identity for result in results for identity in (*result.bits, result.valid)
        )
        prepared = None
        try:
            prepared = prepare_functions(transaction, roots)
            # The complete port-admissibility predicate is source-independent.
            # Promote only an already reachable root; no discarded expression
            # is kept alive just to populate this optional construction memo.
            admitted_request = SemanticRequest("bit-admissibility", (), circuit.inputs)
            if (
                self.functions.cache_construction_reductions
                and circuit._admitted is not None
                and circuit._admitted in roots
                and admitted_request not in self.functions.memo
                and len(self.functions.memo) < 256
            ):
                transaction.reserve_workspace(entries=2)
                prepared.preparation_entries += 2
                admitted = prepared.roots[roots.index(circuit._admitted)]
                available = 256 - len(self.functions.memo)
                prepared.reductions = (
                    (admitted_request, admitted),
                    *prepared.reductions[: available - 1],
                )
            for node in prepared.nodes:
                if node.terminal is not None and (
                    node.terminal.kind != "atom" or node.terminal.value not in (0, 1)
                ):
                    raise AssertionError(
                        "factored circuit must contain only Boolean terminals"
                    )
            remap = dict(zip(roots, prepared.roots, strict=True))
            records = tuple(
                FactoredFunction(
                    result.signature,
                    tuple(remap[item] for item in result.bits),
                    remap[result.valid],
                )
                for result in results
            )
            fresh: dict[FactoredFunction, int] = {}
            identities = []
            for record in records:
                identity = self.keys.get(record)
                if identity is None:
                    identity = fresh.get(record)
                if identity is None:
                    identity = len(self.nodes) + len(fresh)
                    fresh[record] = identity
                identities.append(identity)
            count = len(prepared.nodes)
            memo_reservation = (
                () if scalar_source is None else ((self._scalar_sources.owner, 1, 0),)
            ) + (() if substitution is None else ((self._compositions.owner, 1, 0),))
            prepared.reserve_with(
                (
                    (self.node_owner, len(fresh), len(fresh)),
                    (self.key_owner, len(fresh), 0),
                    *memo_reservation,
                )
            )
            prepared.publish_reserved()
            for record, identity in fresh.items():
                self.nodes.append(record)
                self.keys[record] = identity
            if scalar_source is not None:
                self._scalar_sources._data[scalar_source] = self._handle(identities[0])
            if substitution is not None:
                self._compositions._data[substitution] = self._handle(identities[0])
            self.ledger.bump("semantic_bit_boolean_nodes_published", count)
            self.ledger.bump("semantic_factored_nodes_published", len(fresh))
            return tuple(self._handle(identity) for identity in identities)
        finally:
            if prepared is None:
                transaction.close()
            else:
                prepared.cancel()


class _Circuit:
    def __init__(
        self,
        functions: SemanticFunctionArena,
        inputs: tuple[FinitePort, ...],
        transaction: _Transaction | None = None,
    ) -> None:
        if transaction is not None and transaction.arena is not functions:
            raise ValueError("circuit transaction belongs to another semantic arena")
        self.tx = _Transaction(functions) if transaction is None else transaction
        self.inputs = inputs
        self.signature = FunctionSignature(inputs, BOOL)
        self._admitted: int | None = None
        self._substitutions: dict[
            tuple[tuple[PortVariable, int], ...], dict[int, int]
        ] = {}
        self._substitution_entries = 0
        self._fused_substitutions: dict[_CompositionKey, int] = {}
        self._fused_retained_bindings = 0
        self._fused_projections: dict[tuple[int, int], tuple[int, ...]] = {}
        self._fused_projection_slots = 0
        self._fused_splits: dict[
            tuple[int, ...], tuple[PortVariable, tuple[int, ...], tuple[int, ...]]
        ] = {}
        self._cofactor_circuits: dict[tuple[FinitePort, ...], _Circuit] = {}
        self.zero = self.tx.terminal(self.signature, SemanticTerminal("atom", 0))
        self.one = self.tx.terminal(self.signature, SemanticTerminal("atom", 1))

    def choose(self, condition: int, yes: int, no: int) -> int:
        # Circuit predicates are total Boolean functions: invalid numeric
        # inputs live in a separate validity bit, never an invalid terminal.
        if condition == self.one:
            self.tx.arena.ledger.bump("semantic_bit_constant_choice_reductions")
            return yes
        if condition == self.zero:
            self.tx.arena.ledger.bump("semantic_bit_constant_choice_reductions")
            return no
        if yes == no:
            self.tx.arena.ledger.bump("semantic_bit_equal_branch_reductions")
            return yes
        # These identities apply to the circuit's total Boolean predicates.
        # Apply them before the general Shannon scheduler, whose partial
        # functions must retain their separate invalid-terminal semantics.
        if (yes == self.one or yes == condition) and no == self.zero:
            self.tx.arena.ledger.bump("semantic_bit_boolean_identity_reductions")
            return condition
        if yes == self.one and no == condition:
            self.tx.arena.ledger.bump("semantic_bit_boolean_identity_reductions")
            return condition
        if yes == self.zero and no == condition:
            self.tx.arena.ledger.bump("semantic_bit_boolean_absorption_reductions")
            return self.zero
        if yes == condition and no == self.one:
            self.tx.arena.ledger.bump("semantic_bit_boolean_absorption_reductions")
            return self.one
        return self.tx.choose(condition, yes, no)

    def negate(self, value: int) -> int:
        return self.choose(value, self.zero, self.one)

    def conjunction(self, first: int, second: int) -> int:
        return self.choose(first, second, self.zero)

    def xor(self, first: int, second: int) -> int:
        return self.choose(first, self.negate(second), second)

    def subtract_constant(
        self, bits: tuple[int, ...], value: int
    ) -> tuple[tuple[int, ...], int]:
        borrow = self.zero
        result = []
        for bit, item in enumerate(bits):
            constant = (value >> bit) & 1
            parity = self.xor(item, borrow)
            result.append(self.negate(parity) if constant else parity)
            inverse = self.negate(item)
            borrow = (
                self.choose(inverse, self.one, borrow)
                if constant
                else self.conjunction(inverse, borrow)
            )
        return tuple(result), borrow

    def admitted(self) -> int:
        if self._admitted is not None:
            self.tx.arena.ledger.bump("semantic_bit_admissibility_reuses")
            return self._admitted
        arena = self.tx.arena
        request = SemanticRequest("bit-admissibility", (), self.inputs)
        arena.ledger.bump("semantic_bit_admissibility_requests")
        cached = arena.memo.get(request)
        if cached is not None:
            node = arena.resolve(cached)
            if node.signature != self.signature:
                raise ValueError("cached port admission has another signature")
            self._admitted = cached.local_id
            arena.ledger.bump("semantic_bit_admissibility_early_hits")
            return self._admitted
        arena.ledger.bump("semantic_bit_admissibility_evaluations")
        valid = self.one
        # Build the total padding predicate directly in variable order.  A
        # numeric subtraction also constructs all difference bits, although
        # admission needs only x < cardinality.  Reading the low bit reduces
        # that inequality to ceil(cardinality / 2) or floor(cardinality / 2)
        # on the remaining bits.  At each level there are at most two such
        # residual thresholds, independent of the port's finite cardinality.
        for port in reversed(self.inputs):
            if port.cardinality == 1 << port.bits:
                continue
            valid = self._admitted_port(port, valid)
        self._admitted = valid
        return valid

    def _admitted_port(self, port: FinitePort, success: int) -> int:
        ledger = self.tx.arena.ledger
        # At depth b only floor(C/2**b) and ceil(C/2**b) can occur.
        # Build those two residuals bottom-up using four bounded references,
        # instead of retaining a search stack and dictionary of thresholds.
        self.tx.reserve_workspace(entries=4)
        counter = "semantic_bit_admissibility_threshold_workspace_peak"
        ledger.bump(counter, max(0, 4 - ledger.counters.get(counter, 0)))
        lower, upper = self.zero, success
        try:
            for bit in range(port.bits - 1, -1, -1):
                next_floor = port.cardinality >> (bit + 1)
                floor = port.cardinality >> bit
                ceiling = (port.cardinality + (1 << bit) - 1) >> bit
                next_lower, next_upper = lower, upper
                for role, limit in ((0, floor), (1, ceiling)):
                    ledger.bump("semantic_bit_admissibility_threshold_frames")
                    if limit <= 0:
                        value = self.zero
                    elif limit >= 1 << (port.bits - bit):
                        value = success
                    elif role and floor == ceiling:
                        value = next_lower
                        ledger.bump("semantic_bit_admissibility_threshold_shared_hits")
                    else:
                        variable = PortVariable(
                            port.variable.time,
                            port.variable.side,
                            port.variable.role,
                            bit,
                        )
                        ledger.bump("semantic_bit_admissibility_threshold_decisions")
                        value = self.tx.decision(
                            self.signature,
                            variable,
                            lower if (limit + 1) // 2 == next_floor else upper,
                            lower if limit // 2 == next_floor else upper,
                        )
                    if role:
                        next_upper = value
                    else:
                        next_lower = value
                lower, upper = next_lower, next_upper
            return lower
        finally:
            if not self.tx._closed:
                self.tx.release_workspace(entries=4)

    def imported(self, function: FactoredFunction) -> tuple[tuple[int, ...], int]:
        bits = tuple(
            self.tx.resign(bit.local_id, self.signature) for bit in function.bits
        )
        valid = self.tx.resign(function.valid.local_id, self.signature)
        return bits, valid

    def normalized(
        self, signature: FunctionSignature, bits: tuple[int, ...], valid: int
    ) -> _PendingFunction:
        if (
            type(signature.output) is not AtomSort
            or len(bits) != (signature.output.cardinality - 1).bit_length()
        ):
            raise ValueError("factored output width does not match its sort")
        return _PendingFunction(
            signature, tuple(self.conjunction(valid, bit) for bit in bits), valid
        )


def substitute_boolean(
    circuit: _Circuit, root: int, replacements: Mapping[PortVariable, int]
) -> int:
    """Simultaneous substitution shared across all roots in this circuit.

    The memo is transient, scoped to one immutable semantic transaction and
    complete substitution environment. It contains no source/coordinate keys.
    """
    transaction = circuit.tx
    ledger = transaction.arena.ledger
    key = tuple(sorted(replacements.items()))
    done = circuit._substitutions.setdefault(key, {})

    def retain(identity: int, value: int) -> None:
        done[identity] = value
        circuit._substitution_entries += 1

    pending = [(root, False)]
    changed = frozenset(replacements)
    while pending:
        ledger.bump(
            "semantic_bit_substitution_workspace_peak",
            max(
                0,
                len(pending)
                + circuit._substitution_entries
                - ledger.counters.get("semantic_bit_substitution_workspace_peak", 0),
            ),
        )
        current, ready = pending.pop()
        ledger.bump("semantic_bit_substitution_frames")
        if current in done:
            ledger.bump("semantic_bit_substitution_shared_hits")
            continue
        node = transaction.node(current)
        if node.signature == circuit.signature and not changed.intersection(
            node.support
        ):
            retain(current, current)
            ledger.bump("semantic_bit_substitution_unchanged_roots")
        elif node.terminal is not None:
            retain(current, transaction.terminal(circuit.signature, node.terminal))
        else:
            assert node.variable is not None
            condition = replacements.get(node.variable)
            if condition in (circuit.zero, circuit.one):
                child = node.high if condition == circuit.one else node.low
                if child in done:
                    retain(current, done[child])
                else:
                    ledger.bump("semantic_bit_substitution_cofactor_prunes")
                    pending.extend(((current, True), (child, False)))
            elif ready:
                if condition is None:
                    retain(
                        current,
                        transaction.rebuilt_decision(
                            circuit.signature,
                            node.variable,
                            done[node.low],
                            done[node.high],
                        ),
                    )
                else:
                    retain(
                        current,
                        circuit.choose(condition, done[node.high], done[node.low]),
                    )
            else:
                pending.extend(((current, True), (node.high, False), (node.low, False)))
    return done[root]
