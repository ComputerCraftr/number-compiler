"""Index-owned interning and composition of reduced finite functions."""

from __future__ import annotations

from collections.abc import Iterator, Mapping

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    MAX_PRIMITIVE_ATOMS,
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
    SemanticNode,
    SemanticRequest,
    SemanticTerminal,
    _base,
    _ports,
    _signature,
    _sort,
    _union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


class _SemanticWorkspaceInventory:
    """Live logical storage owned by unfinished semantic transactions."""

    __slots__ = ("entries", "nodes")

    def __init__(self) -> None:
        self.entries = 0
        self.nodes = 0

    def __len__(self) -> int:
        return self.entries


class SemanticFunctionArena:
    """Canonical finite algebra; all retained nodes are owned by this ledger."""

    def __init__(
        self, ledger: ResourceLedger, *, cache_construction_reductions: bool = False
    ) -> None:
        if type(cache_construction_reductions) is not bool:
            raise TypeError("construction reduction policy requires a Boolean")
        self.ledger = ledger
        self.cache_construction_reductions = cache_construction_reductions
        self.token = ArenaToken("semantic-functions")
        ledger.register_execution_root(self)
        prefix = f"semantic-functions-{len(ledger.inventory())}"
        self.node_owner = ledger.register(prefix + "-nodes", "semantic_function")
        self.key_owner = ledger.register(prefix + "-keys", "semantic_function_interner")
        self.workspace_owner = ledger.register(
            prefix + "-workspace", "semantic_function_workspace"
        )
        self.workspace = _SemanticWorkspaceInventory()
        ledger.register_container(
            self.workspace_owner,
            self.workspace,
            node_count=lambda: self.workspace.nodes,
            payloads=lambda: (),
        )
        self.nodes: LedgerList[SemanticNode] = ledger.make_list(self.node_owner)
        self.keys: LedgerDict[SemanticNode, int] = ledger.make_dict(self.key_owner)
        self.memo_owner = ledger.register(prefix + "-requests", "query_memo")
        self.memo: LedgerDict[SemanticRequest, SemanticFunctionID] = ledger.make_dict(
            self.memo_owner
        )
        ledger.register_container(
            self.memo_owner,
            self.memo,
            payloads=lambda: self.memo.items(),
            evict=self._evict,
        )

    def _evict(self) -> None:
        size = len(self.memo)
        self.memo.clear()
        self.ledger.release(self.memo_owner, entries=size)

    def _cached(self, request: SemanticRequest) -> SemanticFunctionID | None:
        self.ledger.bump("semantic_function_requests")
        found = self.memo.get(request)
        if found is not None:
            self.ledger.bump("semantic_function_request_hits")
        return found

    def signature(self, function: SemanticFunctionID) -> FunctionSignature:
        return self.resolve(function).signature

    def iter_reachable(
        self, function: SemanticFunctionID
    ) -> Iterator[SemanticFunctionID]:
        self.resolve(function)
        pending = [function.local_id]
        seen: set[int] = set()
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            yield self._handle(current)
            node = self.nodes[current]
            pending.extend(
                (node.low, node.high)
                if node.terminal is None
                else node.terminal.references
            )

    def _handle(self, identity: int) -> SemanticFunctionID:
        return SemanticFunctionID(self.token, "semantic-function", identity)

    def resolve(self, function: SemanticFunctionID) -> SemanticNode:
        if type(function) is not SemanticFunctionID:
            raise ValueError("a semantic function handle is required")
        ArenaHandle.validate(
            function, self.token, "semantic-function", size=len(self.nodes)
        )
        return self.nodes[function.local_id]

    def atom(self, signature: FunctionSignature, value: int) -> SemanticFunctionID:
        _signature(signature)
        if (
            type(signature.output) is not AtomSort
            or type(value) is not int
            or not 0 <= value < signature.output.cardinality
        ):
            raise ValueError("atom is outside its declared output sort")
        transaction = _Transaction(self)
        root = transaction.terminal(signature, SemanticTerminal("atom", value))
        return transaction.finish(transaction.admissible(root))

    def invalid(self, signature: FunctionSignature) -> SemanticFunctionID:
        _signature(signature)
        transaction = _Transaction(self)
        return transaction.finish(
            transaction.terminal(signature, SemanticTerminal("invalid"))
        )

    def variable(
        self,
        inputs: tuple[FinitePort, ...],
        port: FinitePort,
        output: AtomSort | None = None,
    ) -> SemanticFunctionID:
        _ports(inputs)
        _ports((port,))
        if port not in inputs:
            raise ValueError("input port is not declared")
        target = (
            AtomSort(port.variable.role, port.cardinality) if output is None else output
        )
        _sort(target)
        if type(target) is not AtomSort or target.cardinality != port.cardinality:
            raise ValueError("variable output has another finite cardinality")
        if port.cardinality > MAX_PRIMITIVE_ATOMS:
            raise ValueError(
                "wide identity requires bit-factored output; primitive atom compilation is capped"
            )
        signature = FunctionSignature(inputs, target)
        transaction = _Transaction(self)
        # Only this primitive domain is expanded, never a product of ports.
        pending = [(0, 0, False)]
        done: dict[tuple[int, int], int] = {}
        while pending:
            bit, prefix, ready = pending.pop()
            if bit == port.bits:
                terminal = (
                    SemanticTerminal("atom", prefix)
                    if prefix < port.cardinality
                    else SemanticTerminal("invalid")
                )
                done[bit, prefix] = transaction.terminal(signature, terminal)
            elif ready:
                variable = PortVariable(
                    port.variable.time, port.variable.side, port.variable.role, bit
                )
                done[bit, prefix] = transaction.decision(
                    signature,
                    variable,
                    done[bit + 1, prefix],
                    done[bit + 1, prefix | (1 << bit)],
                )
            else:
                pending.extend(
                    (
                        (bit, prefix, True),
                        (bit + 1, prefix | (1 << bit), False),
                        (bit + 1, prefix, False),
                    )
                )
        return transaction.finish(transaction.admissible(done[0, 0]))

    def ite(
        self,
        condition: SemanticFunctionID,
        yes: SemanticFunctionID,
        no: SemanticFunctionID,
    ) -> SemanticFunctionID:
        c, a, b = (self.resolve(item) for item in (condition, yes, no))
        if c.signature.output != BOOL or a.signature.output != b.signature.output:
            raise ValueError(
                "conditional requires boolean condition and matching outputs"
            )
        inputs = _union_inputs(
            c.signature.inputs, a.signature.inputs, b.signature.inputs
        )
        request = SemanticRequest("ite", (condition, yes, no))
        found = self._cached(request)
        if found is not None:
            return found
        transaction = _Transaction(self, request)
        root = transaction.choose(
            transaction.resign(condition.local_id, FunctionSignature(inputs, BOOL)),
            transaction.resign(
                yes.local_id, FunctionSignature(inputs, a.signature.output)
            ),
            transaction.resign(
                no.local_id, FunctionSignature(inputs, b.signature.output)
            ),
        )
        return transaction.finish(transaction.admissible(root))

    def product(self, functions: tuple[SemanticFunctionID, ...]) -> SemanticFunctionID:
        if type(functions) is not tuple or not functions:
            raise ValueError("product requires an immutable nonempty function tuple")
        nodes = tuple(self.resolve(item) for item in functions)
        inputs = _union_inputs(*(node.signature.inputs for node in nodes))
        signature = FunctionSignature(
            inputs, ProductSort(tuple(node.signature.output for node in nodes))
        )
        request = SemanticRequest("product", functions)
        found = self._cached(request)
        if found is not None:
            return found
        transaction = _Transaction(self, request)
        roots = tuple(
            transaction.resign(
                item.local_id, FunctionSignature(inputs, node.signature.output)
            )
            for item, node in zip(functions, nodes)
        )
        root = transaction.zip_product(roots, signature)
        return transaction.finish(transaction.admissible(root))

    def curry(
        self, function: SemanticFunctionID, bound_ports: tuple[FinitePort, ...]
    ) -> SemanticFunctionID:
        node = self.resolve(function)
        _ports(bound_ports)
        if any(port not in node.signature.inputs for port in bound_ports):
            raise ValueError("curried ports are not inputs of this function")
        outer = tuple(port for port in node.signature.inputs if port not in bound_ports)
        inner_signature = FunctionSignature(bound_ports, node.signature.output)
        signature = FunctionSignature(
            outer, FunctionSort(bound_ports, node.signature.output)
        )
        outer_names = {port.variable for port in outer}
        request = SemanticRequest("curry", (function,), bound_ports)
        found = self._cached(request)
        if found is not None:
            return found
        transaction = _Transaction(self, request)
        pending = [(function.local_id, False)]
        results: dict[int, int] = {}
        dependencies: dict[int, tuple[PortVariable, int, int]] = {}
        while pending:
            current, ready = pending.pop()
            if current in results:
                continue
            variables = [
                v for v in transaction.node(current).support if _base(v) in outer_names
            ]
            if not variables:
                inner = transaction.resign(current, inner_signature)
                results[current] = transaction.terminal(
                    signature, SemanticTerminal("function", references=(inner,))
                )
            elif ready:
                variable, low, high = dependencies[current]
                results[current] = transaction.decision(
                    signature, variable, results[low], results[high]
                )
            else:
                variable = min(variables)
                low = transaction.restrict(current, variable, 0)
                high = transaction.restrict(current, variable, 1)
                dependencies[current] = variable, low, high
                pending.extend(((current, True), (high, False), (low, False)))
        return transaction.finish(transaction.admissible(results[function.local_id]))

    def substitute(
        self,
        function: SemanticFunctionID,
        replacements: Mapping[PortVariable, SemanticFunctionID],
    ) -> SemanticFunctionID:
        node = self.resolve(function)
        items = self._replacements(node.signature.inputs, replacements)
        request = SemanticRequest(
            "substitute",
            (function,) + tuple(self._handle(item) for _, item in items),
            tuple(port for port, _ in items),
        )
        found = self._cached(request)
        if found is not None:
            return found
        transaction = _Transaction(self, request)
        root = transaction.substitution(function.local_id, items)
        return transaction.finish(transaction.admissible(root))

    def _replacements(
        self,
        inputs: tuple[FinitePort, ...],
        replacements: Mapping[PortVariable, SemanticFunctionID],
    ) -> tuple[tuple[FinitePort, int], ...]:
        admitted = {port.variable: port for port in inputs}
        items = []
        for variable, replacement in replacements.items():
            if type(variable) is not PortVariable:
                raise ValueError("replacement needs a typed finite port")
            PortVariable.__post_init__(variable)
            port = admitted.get(variable)
            if port is None:
                raise ValueError("replacement port is outside the function signature")
            node = self.resolve(replacement)
            if (
                type(node.signature.output) is not AtomSort
                or node.signature.output.cardinality != port.cardinality
            ):
                raise ValueError("replacement output has another finite domain")
            items.append((port, replacement.local_id))
        return tuple(sorted(items, key=lambda item: item[0].variable))

    def apply(
        self,
        function_value: SemanticFunctionID,
        arguments: Mapping[PortVariable, SemanticFunctionID],
    ) -> SemanticFunctionID:
        node = self.resolve(function_value)
        target = node.signature.output
        if type(target) is not FunctionSort:
            raise ValueError("application requires a function-valued output")
        replacements = self._replacements(target.inputs, arguments)
        if len(replacements) != len(target.inputs):
            raise ValueError("application must bind every function input")
        request = SemanticRequest(
            "apply",
            (function_value,) + tuple(self._handle(item) for _, item in replacements),
            tuple(port for port, _ in replacements),
        )
        found = self._cached(request)
        if found is not None:
            return found
        transaction = _Transaction(self, request)
        inputs = _union_inputs(
            node.signature.inputs,
            *(transaction.node(item).signature.inputs for _, item in replacements),
        )
        signature = FunctionSignature(inputs, target.output)

        def apply_terminal(terminal: SemanticTerminal) -> int:
            if terminal.kind == "invalid":
                return transaction.terminal(signature, terminal)
            if terminal.kind != "function":
                raise AssertionError("function sort has a nonfunction terminal")
            return transaction.resign(
                transaction.substitution(terminal.references[0], replacements),
                signature,
            )

        root = transaction.map_terminals(
            function_value.local_id, signature, apply_terminal
        )
        return transaction.finish(transaction.admissible(root))

    def evaluate(
        self, function: SemanticFunctionID, values: Mapping[PortVariable, int]
    ) -> SemanticTerminal:
        node = self.resolve(function)
        inputs = node.signature.inputs
        if len(values) != len(inputs):
            raise ValueError("evaluation requires every declared input")
        for key in values:
            if type(key) is not PortVariable:
                raise ValueError("evaluation requires typed port names")
            PortVariable.__post_init__(key)
        for port in inputs:
            if port.variable not in values or type(values[port.variable]) is not int:
                raise ValueError("evaluation inputs must be exact finite integers")
            if not 0 <= values[port.variable] < (1 << port.bits):
                raise ValueError("evaluation input exceeds its encoded width")
        self.ledger.bump("semantic_function_evaluations")
        while node.variable is not None:
            variable = node.variable
            bit = (values[_base(variable)] >> variable.bit) & 1
            node = self.nodes[node.high if bit else node.low]
            self.ledger.bump("semantic_function_decision_visits")
        if node.terminal is None:
            raise AssertionError("semantic leaf has no terminal")
        return node.terminal

    def terminal_references(
        self, function: SemanticFunctionID, values: Mapping[PortVariable, int]
    ) -> tuple[SemanticFunctionID, ...]:
        terminal = self.evaluate(function, values)
        return tuple(self._handle(item) for item in terminal.references)

    def require_total(
        self, function: SemanticFunctionID, admissible: SemanticFunctionID
    ) -> None:
        """Reject undefined output on any admitted input, including inner functions.

        This is a symbolic product walk of reduced DAGs, not a sampled proof or
        enumeration of the port universe. Its workspace is discarded; no
        validity predicate or partially checked result enters an arena.
        """
        from number_compiler.arithmetic.functions.semantic_totality import (
            require_semantic_total,
        )

        require_semantic_total(self, (function,), admissible)


__all__ = ["SemanticFunctionArena"]
