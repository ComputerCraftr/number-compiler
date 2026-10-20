"""Factored finite numeric outputs without atom-domain truth enumeration.

A value is a fixed tuple of canonical Boolean functions plus one admissibility
predicate. Invalid assignments have all bits canonically zero. Division is a
bounded comparator/subtractor circuit, never a table with one row per radix.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
        CompleteFiniteTransform,
    )

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticRequest,
    union_inputs,
    validate_function_signature,
    validate_ports,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.boolean_circuit import (
    BooleanCircuit as BooleanCircuit,
)
from number_compiler.hashlife.interfaces.boolean_substitution import (
    substitute_boolean,
)
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    BinaryDivision as BinaryDivision,
)
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    BitSubstitutionKey as BitSubstitutionKey,
)
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    FactoredFunction as FactoredFunction,
)
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    FactoredFunctionID as FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    PendingFunction as PendingFunction,
)
from number_compiler.hashlife.interfaces.semantic_publication import prepare_functions
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.resources.stores import LedgerDict, LedgerList


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

    def composition_audit_snapshot(
        self,
    ) -> OwnedMemoAuditSnapshot[BitSubstitutionKey, FactoredFunctionID]:
        """Return read-only accounting and store identity for the composition audit."""
        return self._compositions.audit_snapshot()

    def scalar_source_audit_snapshot(
        self,
    ) -> OwnedMemoAuditSnapshot[SemanticFunctionID, FactoredFunctionID]:
        """Return read-only accounting and store identity for scalar-source audits."""
        return self._scalar_sources.audit_snapshot()

    def lookup_composition(self, key: BitSubstitutionKey) -> FactoredFunctionID | None:
        """Return a validated cached substitution result, if one is retained."""
        result = self._compositions.get(key)
        if result is not None:
            self.resolve(result)
        return result

    def scoped_handle(self, identity: int) -> FactoredFunctionID:
        return FactoredFunctionID(self.token, "semantic-bit-function", identity)

    def candidate_handle(
        self, identity: int, *, base: int, candidate_count: int
    ) -> FactoredFunctionID:
        """Create a prospective ID bounded by the active publication window."""
        require_integer(identity, "factored candidate ID", 0)
        require_integer(base, "factored publication base", 0)
        require_integer(candidate_count, "factored candidate count", 0)
        if base != len(self.nodes):
            raise RuntimeError("factored publication base is stale")
        if identity >= base + candidate_count:
            raise ValueError("factored candidate ID is outside its publication window")
        return self.scoped_handle(identity)

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
        validate_function_signature(node.signature)
        if type(node.signature.output) is not AtomSort:
            raise ValueError("factored conversion requires a scalar semantic output")
        self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_FROM_SCALAR_REQUESTS)
        cached = self._scalar_sources.get(function)
        if cached is not None:
            self.resolve(cached)
            self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_FROM_SCALAR_HITS)
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
        circuit = BooleanCircuit(self.functions, node.signature.inputs)
        tx = circuit.tx
        width = (node.signature.output.cardinality - 1).bit_length()
        pending = [(function.local_id, False)]
        done: dict[int, tuple[int, ...]] = {}
        while pending:
            identity, ready = pending.pop()
            self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_FROM_SCALAR_FRAMES)
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
        self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_FROM_SCALAR_EVALUATIONS)
        return self.publish_circuit(circuit, (result,), scalar_source=function)[0]

    def variable(
        self,
        inputs: tuple[FinitePort, ...],
        port: FinitePort,
        output: AtomSort | None = None,
    ) -> FactoredFunctionID:
        validate_ports(inputs)
        validate_ports((port,))
        if port not in inputs:
            raise ValueError("factored variable is not a declared port")
        target = (
            AtomSort(port.variable.role, port.cardinality) if output is None else output
        )
        signature = FunctionSignature(inputs, target)
        if type(target) is not AtomSort or target.cardinality != port.cardinality:
            raise ValueError("factored input/output domains disagree")
        circuit = BooleanCircuit(self.functions, inputs)
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
        return self.publish_circuit(circuit, (value,))[0]

    def constant(self, signature: FunctionSignature, value: int) -> FactoredFunctionID:
        validate_function_signature(signature)
        target = signature.output
        if (
            type(target) is not AtomSort
            or type(value) is not int
            or not 0 <= value < target.cardinality
        ):
            raise ValueError("factored constant must fit a bounded atom sort")
        circuit = BooleanCircuit(self.functions, signature.inputs)
        bits = tuple(
            circuit.one if (value >> bit) & 1 else circuit.zero
            for bit in range((target.cardinality - 1).bit_length())
        )
        result = circuit.normalized(signature, bits, circuit.admitted())
        return self.publish_circuit(circuit, (result,))[0]

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
        inputs = union_inputs(a.signature.inputs, b.signature.inputs)
        signature = FunctionSignature(inputs, output)
        if type(output) is not AtomSort:
            raise ValueError("numeric addition needs an atom output")
        width = (output.cardinality - 1).bit_length()
        if wrap and output.cardinality != 1 << width:
            raise ValueError("wrapping addition requires a power-of-two output sort")
        circuit = BooleanCircuit(self.functions, inputs)
        aa, av = circuit.imported(a)
        bb, bv = circuit.imported(b)
        carry = circuit.zero
        bits: list[int] = []
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
        return self.publish_circuit(circuit, (result,))[0]

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
        inputs = union_inputs(
            c.signature.inputs, a.signature.inputs, b.signature.inputs
        )
        circuit = BooleanCircuit(self.functions, inputs)
        cc, cv = circuit.imported(c)
        aa, av = circuit.imported(a)
        bb, bv = circuit.imported(b)
        valid = circuit.conjunction(cv, circuit.choose(cc[0], av, bv))
        valid = circuit.conjunction(circuit.admitted(), valid)
        bits = tuple(
            circuit.choose(cc[0], left, right)
            for left, right in zip(aa, bb, strict=True)
        )
        signature = FunctionSignature(inputs, a.signature.output)
        result = circuit.normalized(signature, bits, valid)
        return self.publish_circuit(circuit, (result,))[0]

    def imported_circuit(
        self, source: FactoredFunction
    ) -> tuple[BooleanCircuit, tuple[int, ...], int]:
        """Import one numeric function while preserving its admitted domain."""
        circuit = BooleanCircuit(self.functions, source.signature.inputs)
        roots, valid = circuit.imported(source)
        return circuit, roots, valid

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
        circuit, source_bits, valid = self.imported_circuit(source)
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
        return self.publish_circuit(circuit, (result,))[0]

    def restrict(
        self, function: FactoredFunctionID, predicate: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Restrict a function's domain, retaining admissibility in its identity."""
        value, guard = self.resolve(function), self.resolve(predicate)
        if guard.signature.output != BOOL:
            raise ValueError("function restriction requires a Boolean predicate")
        inputs = union_inputs(value.signature.inputs, guard.signature.inputs)
        circuit = BooleanCircuit(self.functions, inputs)
        bits, valid = circuit.imported(value)
        condition, admitted = circuit.imported(guard)
        valid = circuit.conjunction(valid, circuit.conjunction(admitted, condition[0]))
        result = circuit.normalized(
            FunctionSignature(inputs, value.signature.output), bits, valid
        )
        return self.publish_circuit(circuit, (result,))[0]

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
        inputs = union_inputs(*(n.signature.inputs for n in nodes))
        layout = tuple(node.signature.output for node in nodes)
        signature = FunctionSignature(
            inputs, AtomSort(f"{name}:{layout!r}", 1 << width)
        )
        circuit = BooleanCircuit(self.functions, inputs)
        bits: tuple[int, ...] = ()
        valid = circuit.one
        for node in nodes:
            component, admitted = circuit.imported(node)
            bits += component
            valid = circuit.conjunction(valid, admitted)
        return self.publish_circuit(
            circuit, (circuit.normalized(signature, bits, valid),)
        )[0]

    def domain_predicate(self, function: FactoredFunctionID) -> FactoredFunctionID:
        """Return definedness as a Boolean function on the declared port domain."""
        node = self.resolve(function)
        self.functions.resolve(node.valid)
        circuit = BooleanCircuit(self.functions, node.signature.inputs)
        # Definedness is already a complete canonical root. Importing the value
        # bits here makes every admission query pay for an unrequested output.
        valid = circuit.tx.resign(node.valid.local_id, circuit.signature)
        signature = FunctionSignature(node.signature.inputs, BOOL)
        result = circuit.normalized(signature, (valid,), circuit.admitted())
        return self.publish_circuit(circuit, (result,))[0]

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
        from number_compiler.hashlife.interfaces.semantic_bit_batches import (
            admitted_replacements,
            substitution_environment,
        )

        items, references = admitted_replacements(
            self, original.signature.inputs, replacements
        )
        removed = {port.variable for port, _ in items}
        inputs = union_inputs(
            tuple(
                port
                for port in original.signature.inputs
                if port.variable not in removed
            ),
            *(value.signature.inputs for _, value in items),
        )
        key = BitSubstitutionKey(function, tuple(sorted(references)))
        self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_COMPOSITION_REQUESTS)
        cached = self.lookup_composition(key)
        if cached is not None:
            self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_COMPOSITION_HITS)
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
        circuit = BooleanCircuit(self.functions, inputs)
        mapping, validity, transform = substitution_environment(circuit, items, joint)
        result_bits = tuple(
            transform(circuit, bit.local_id, mapping) for bit in original.bits
        )
        valid = transform(circuit, original.valid.local_id, mapping)
        result = circuit.normalized(
            FunctionSignature(inputs, original.signature.output),
            result_bits,
            circuit.conjunction(validity, valid),
        )
        self.ledger.bump(_interfaces_keys.SEMANTIC_BIT_COMPOSITION_EVALUATIONS)
        return self.publish_circuit(circuit, (result,), substitution=key)[0]

    def substitute_many(
        self,
        functions: tuple[FactoredFunctionID, ...],
        replacements: Mapping[PortVariable, FactoredFunctionID],
        *,
        joint: bool = True,
    ) -> tuple[FactoredFunctionID, ...]:
        """Substitute one environment through several shared DAG roots."""
        from number_compiler.hashlife.interfaces.semantic_bit_batches import (
            substitute_many,
        )

        return substitute_many(self, functions, replacements, joint=joint)

    def restrict_many(
        self,
        functions: tuple[FactoredFunctionID, ...],
        predicate: FactoredFunctionID,
    ) -> tuple[FactoredFunctionID, ...]:
        """Restrict several functions in one atomic shared-DAG transaction."""
        from number_compiler.hashlife.interfaces.semantic_bit_batches import (
            restrict_many,
        )

        return restrict_many(self, functions, predicate)

    def complete_transform(
        self,
        ports: tuple[FinitePort, ...],
        outputs: tuple[FactoredFunctionID, ...],
        admissible: FactoredFunctionID,
        *,
        retained: tuple[FactoredFunctionID, ...] = (),
    ) -> tuple[CompleteFiniteTransform, tuple[FactoredFunctionID, ...]]:
        from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
            normalize,
        )

        return normalize(self, ports, outputs, admissible, retained)

    def validate_complete_transform(self, transform: CompleteFiniteTransform) -> None:
        from number_compiler.hashlife.interfaces.semantic_bit_transforms import validate

        validate(self, transform)

    def compose_complete_transform(
        self,
        before: CompleteFiniteTransform,
        after: CompleteFiniteTransform,
        *,
        retained: tuple[FactoredFunctionID, ...] = (),
    ) -> tuple[CompleteFiniteTransform, tuple[FactoredFunctionID, ...]]:
        from number_compiler.hashlife.interfaces.semantic_bit_transforms import compose

        return compose(self, before, after, retained)

    def divmod_atoms(
        self,
        function: FactoredFunctionID,
        divisor: int,
        quotient_sort: AtomSort,
        remainder_sort: AtomSort,
    ) -> tuple[FactoredFunctionID, FactoredFunctionID]:
        """Factor an atom function by bit arithmetic, without an alphabet table."""
        from number_compiler.hashlife.interfaces.semantic_bit_batches import (
            divmod_atoms,
        )

        return divmod_atoms(self, function, divisor, quotient_sort, remainder_sort)

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
        validate_ports((carry,))
        validate_ports((symbol,))
        if (
            carry.variable == symbol.variable
            or carry.cardinality != radix
            or symbol.cardinality != 2
        ):
            raise ValueError("division requires distinct carry:r and symbol:2 ports")
        bundle = union_inputs((carry,), (symbol,)) if inputs is None else inputs
        validate_ports(bundle)
        if carry not in bundle or symbol not in bundle:
            raise ValueError("division ports must be declared")
        circuit = BooleanCircuit(self.functions, bundle)
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
        result = self.publish_circuit(circuit, (remain, quot))
        self.ledger.bump(_interfaces_keys.SEMANTIC_BINARY_DIVISION_COMPILATIONS)
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

    def publish_circuit(
        self,
        circuit: BooleanCircuit,
        results: tuple[PendingFunction, ...],
        *,
        scalar_source: SemanticFunctionID | None = None,
        substitution: BitSubstitutionKey | None = None,
        substitutions: tuple[BitSubstitutionKey, ...] = (),
    ) -> tuple[FactoredFunctionID, ...]:
        if substitution is not None and substitutions:
            raise ValueError("factored publication has two substitution owners")
        if substitutions and len(substitutions) != len(results):
            raise ValueError("batch substitution keys disagree with their results")
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
            admitted_root = circuit.admitted_root
            if (
                self.functions.cache_construction_reductions
                and admitted_root is not None
                and admitted_root in roots
                and admitted_request not in self.functions.memo
                and len(self.functions.memo) < 256
            ):
                transaction.reserve_workspace(entries=2)
                prepared.preparation_entries += 2
                admitted = prepared.roots[roots.index(admitted_root)]
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
            identities: list[int] = []
            for record in records:
                identity = self.keys.get(record)
                if identity is None:
                    identity = fresh.get(record)
                if identity is None:
                    identity = len(self.nodes) + len(fresh)
                    fresh[record] = identity
                identities.append(identity)
            count = len(prepared.nodes)
            substitution_count = int(substitution is not None) + len(substitutions)
            memo_reservation = (
                () if scalar_source is None else ((self._scalar_sources.owner, 1, 0),)
            ) + (
                ()
                if not substitution_count
                else ((self._compositions.owner, substitution_count, 0),)
            )
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
                self._scalar_sources.publish_reserved(
                    scalar_source, self.scoped_handle(identities[0])
                )
            if substitution is not None:
                self._compositions.publish_reserved(
                    substitution, self.scoped_handle(identities[0])
                )
            if substitutions:
                for key, identity in zip(substitutions, identities, strict=True):
                    self._compositions.publish_reserved(
                        key, self.scoped_handle(identity)
                    )
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_BOOLEAN_NODES_PUBLISHED, count
            )
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_FACTORED_NODES_PUBLISHED,
                len(fresh),
            )
            return tuple(self.scoped_handle(identity) for identity in identities)
        finally:
            if prepared is None:
                transaction.close()
            else:
                prepared.cancel()


__all__ = ["BooleanCircuit", "substitute_boolean"]
