"""Joint finite-port interpretation of structured boundary expression outputs.

The structured bridge accepts primitive and two-primitive composed state inputs.
The legacy scalar bridge remains primitive-input only.
Structured output pairs and higher functions are reduced semantically, jointly
across outer and bound ports. No expression-to-observed-value cache is retained.
"""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemanticsAdapter,
)
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.iterative_queries import (
    defer_indexed_dependencies,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
    ProductSort,
    SemanticFunctionID,
    SemanticSort,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    FunctionSort as SemanticFunctionSort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    ResolveExpr,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    BoundaryExprNode,
    ExpressionSort,
    ExprID,
    FormalPort,
    FunctionSort,
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import observation_inputs
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    primitive_operation,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    CompileStructuredExpression,
    StructuredExpressionTask,
    StructuredTask,
)
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    ReachableCodec,
    SemanticProfileArena,
    SemanticProfileID,
)
from number_compiler.hashlife.interfaces.semantic_state_codec import (
    StateCodec,
    StateCodecArena,
    describe_state,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Result,
        Task,
    )


@dataclass(frozen=True, slots=True)
class CompiledSemanticExpression:
    function: SemanticFunctionID
    ports: tuple[FinitePort, ...]
    input_sorts: tuple[StateSort, ...]
    output_sort: ExpressionSort


@dataclass(frozen=True, slots=True)
class CompiledStructuredExpression:
    structure: StructureID
    ports: tuple[FinitePort, ...]
    input_sorts: tuple[StateSort, ...]
    output_sort: ExpressionSort
    profile: SemanticProfileID | None = None


@dataclass(frozen=True, slots=True)
class ExpressionAdmissionKey:
    expression: ExprID
    structured: bool
    profile: SemanticProfileID | None = None

    def __post_init__(self) -> None:
        if (
            type(self.expression) is not ExprID
            or type(self.structured) is not bool
            or self.profile is not None
            and (not self.structured or type(self.profile) is not SemanticProfileID)
        ):
            raise ValueError(
                "domain admission requires an expression and exact compilation mode"
            )


@dataclass(frozen=True, slots=True)
class ExpressionDomainProof:
    key: ExpressionAdmissionKey


@dataclass(frozen=True, slots=True)
class _Task:
    expression: ExprID
    environment: tuple[tuple[ExprID, FinitePort], ...]
    depth: int = 0


@dataclass(frozen=True, slots=True)
class FiniteLiftKey:
    function: TransferSummaryID
    source: StateSort
    target: ExpressionSort


class SemanticExpressionCompiler:
    def __init__(
        self,
        runtime: DiamondRuntime,
        functions: SemanticFunctionArena,
        *,
        structures: StructureArena | None = None,
    ) -> None:
        if runtime.ledger is not functions.ledger:
            raise ValueError("expression and semantic arenas require one ledger")
        if structures is not None and structures.functions is not functions:
            raise ValueError(
                "structured compiler must share the semantic function arena"
            )
        self.structures = structures
        self.codecs: StateCodecArena | None = None
        self.profiles: SemanticProfileArena | None = None
        self.runtime, self.functions = runtime, functions
        self.expressions: BoundaryExpressionArena = runtime.higher.expressions
        self.ledger: ResourceLedger = runtime.ledger
        self.primitives: PrimitiveSemanticsAdapter = PrimitiveSemanticsAdapter(
            runtime.kernels, functions, family_hooks=runtime.family_hooks
        )
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"semantic-expression-admission-{len(self.ledger.inventory())}",
            "query_memo",
        )
        self.admissions: OwnedMemo[ExpressionAdmissionKey, ExpressionDomainProof] = (
            OwnedMemo(self.ledger, owner, evictable=True)
        )
        finite_owner = self.ledger.register(
            f"semantic-finite-lifts-{len(self.ledger.inventory())}",
            "query_memo",
        )
        self._finite_lifts: OwnedMemo[
            FiniteLiftKey, tuple[SemanticFunctionID, FinitePort]
        ] = OwnedMemo(self.ledger, finite_owner, evictable=True)

    def finite_lift_audit_snapshot(
        self,
    ) -> OwnedMemoAuditSnapshot[FiniteLiftKey, tuple[SemanticFunctionID, FinitePort]]:
        """Return read-only accounting and store identity for finite-lift audits."""
        return self._finite_lifts.audit_snapshot()

    def atom_sort(self, sort: ExpressionSort) -> AtomSort:
        """Return the finite atom domain represented by an expression sort."""
        if isinstance(sort, SymbolSort):
            return AtomSort("primitive-symbol", sort.blank + 1)
        if not isinstance(sort, StateSort):
            raise UnsupportedInterfaceError(
                "a finite input must have a primitive state sort"
            )
        primitive = self.expressions.primitive(sort.action)
        if primitive is None:
            raise UnsupportedInterfaceError(
                "composed input domains require a factored semantic interface"
            )
        count = len(primitive.domain(BoundarySide(sort.side)))
        return AtomSort(
            "primitive-left-state" if sort.side == 0 else "primitive-right-state", count
        )

    def source_initial_profile(self, action: ActionProgramID) -> SemanticProfileID:
        """Issue an explicit certified domain; universal compilation is unchanged."""
        self.runtime.actions.resolve(action)
        if self.profiles is None:
            self.profiles = SemanticProfileArena(self.runtime)
        return self.profiles.source_initial_profile(action)

    def semantic_profile(
        self, profile: SemanticProfileID | None
    ) -> SemanticProfileArena | None:
        if profile is None:
            return None
        if self.profiles is None:
            raise ValueError("semantic profile belongs to another compiler")
        self.profiles.resolve(profile)
        return self.profiles

    def _admit(
        self,
        expression: ExprID,
        parameters: tuple[ExprID, ...],
        *,
        structured: bool = False,
        profile: SemanticProfileID | None = None,
    ) -> tuple[StateSort, ...]:
        self.semantic_profile(profile)
        if type(parameters) is not tuple:
            raise ValueError("semantic parameters must be distinct scoped ports")
        root = self.expressions.node(expression)
        sorts: list[StateSort] = []
        declared: set[FormalPort] = set()
        for parameter in parameters:
            node = self.expressions.node(parameter)
            if node.kind != "port" or type(node.sort) is not StateSort:
                raise ValueError("semantic parameters must be state ports")
            sorts.append(node.sort)
            declared.add(FormalPort(node.sort, node.role))
        if len(set(parameters)) != len(parameters):
            raise ValueError("semantic parameters must be distinct scoped ports")
        if any(port not in declared for port in root.free_ports):
            raise ValueError("expression has an undeclared free port")
        key = ExpressionAdmissionKey(expression, structured, profile)
        proof = self.admissions.get(key)
        if proof is not None:
            if type(proof) is not ExpressionDomainProof or proof.key != key:
                raise ValueError("stored domain proof has another expression or mode")
            self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_REQUESTS)
            self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_HITS)
            return tuple(sorts)
        # The proof is bound to this expression's exact formal ports, mode,
        # and profile.  Validate their finite encodings only on the miss;
        # publication of the same immutable task must not rebuild a wide
        # composed-state codec merely to rediscover the proof above.
        for sort in sorts:
            if structured:
                self.input_ports(
                    sort,
                    PortVariable(0, 0, "admission", 0),
                    profile,
                )
            else:
                self.atom_sort(sort)
        visits, frames, peak = self._validate_domains(expression, structured, profile)
        self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_REQUESTS)
        self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_NODES, visits)
        self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_FRAMES, frames)
        self.ledger.bump(
            _interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_WORKSPACE_PEAK,
            max(
                0,
                peak
                - self.ledger.counters.get(
                    _interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_WORKSPACE_PEAK,
                    0,
                ),
            ),
        )
        self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_ADMISSION_EVALUATIONS)
        self.admissions[key] = ExpressionDomainProof(key)
        return tuple(sorts)

    def _validate_domains(
        self,
        expression: ExprID,
        structured: bool,
        profile: SemanticProfileID | None = None,
    ) -> tuple[int, int, int]:
        """Read only: prove immutable descendants once, including opaque bodies."""
        pending = [expression.local_id]
        seen: set[int] = set()
        frames, peak = 0, len(pending)
        while pending:
            frames += 1
            peak = max(peak, len(pending) + len(seen))
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            node = self.expressions.nodes[current]
            if node.kind == "lambda":
                assert isinstance(node.sort, FunctionSort)
                self.input_ports(
                    node.sort.domain, PortVariable(0, 0, "admission", 0), profile
                ) if structured else self.atom_sort(node.sort.domain)
            pending.extend(node.children)
            if node.closure is not None:
                pending.append(
                    self.expressions.closures.resolve(node.closure).body.local_id
                )
        return len(seen), frames, peak

    def compile(
        self, expression: ExprID, parameters: tuple[ExprID, ...] = ()
    ) -> CompiledSemanticExpression:
        sorts = self._admit(expression, parameters)
        ports = tuple(
            FinitePort(
                PortVariable(0, 0, f"semantic-parameter-{index:08}", 0),
                self.atom_sort(sort).cardinality,
            )
            for index, sort in enumerate(sorts)
        )
        initial = _Task(expression, tuple(zip(parameters, ports, strict=True)))
        stack: list[Generator[_Task, SemanticFunctionID, SemanticFunctionID]] = []
        pending: _Task | None = initial
        result: SemanticFunctionID | None = None
        peak = 0
        while True:
            if pending is not None:
                computation = self._program(pending)
                stack.append(computation)
                peak = max(peak, len(stack))
                self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_TASKS)
                try:
                    pending = next(computation)
                    continue
                except StopIteration as finished:
                    result = finished.value
                    stack.pop()
                    pending = None
            if not stack:
                assert result is not None
                break
            assert result is not None
            try:
                pending = stack[-1].send(result)
            except StopIteration as finished:
                result = finished.value
                stack.pop()
                pending = None
        result = self._declare(result, ports)
        self.ledger.bump(
            _interfaces_keys.SEMANTIC_EXPRESSION_STACK_PEAK,
            max(
                0,
                peak
                - self.ledger.counters.get(
                    _interfaces_keys.SEMANTIC_EXPRESSION_STACK_PEAK, 0
                ),
            ),
        )
        return CompiledSemanticExpression(
            result, ports, sorts, self.expressions.node(expression).sort
        )

    def input_ports(
        self,
        sort: StateSort,
        namespace: PortVariable,
        profile: SemanticProfileID | None = None,
    ) -> tuple[FinitePort, ...]:
        profiles = self.semantic_profile(profile)
        if profiles is not None:
            assert profile is not None
            return profiles.ports(profile, sort.action, sort.side, namespace)
        if self.expressions.primitive(sort.action) is not None:
            return (FinitePort(namespace, self.atom_sort(sort).cardinality),)
        try:
            return describe_state(self.runtime, sort.action, sort.side, namespace).ports
        except ValueError as error:
            raise UnsupportedInterfaceError(str(error)) from error

    def _ports_for(
        self, parameters: tuple[ExprID, ...], profile: SemanticProfileID | None = None
    ) -> tuple[FinitePort, ...]:
        ports: list[FinitePort] = []
        for index, parameter in enumerate(parameters):
            sort = self.expressions.node(parameter).sort
            match sort:
                case StateSort():
                    pass
                case _:
                    raise ValueError("semantic input must be a state")
            ports.extend(
                self.input_ports(
                    sort,
                    PortVariable(0, 0, f"semantic-parameter-{index:08}", 0),
                    profile,
                )
            )
        return tuple(sorted(ports, key=lambda port: port.variable))

    def expression_binding(
        self,
        variable: ExprID,
        namespace: PortVariable,
        profile: SemanticProfileID | None = None,
    ) -> FinitePort | StateCodec | ReachableCodec:
        sort = self.expressions.node(variable).sort
        match sort:
            case StateSort():
                pass
            case _:
                raise ValueError("semantic input must be a state")
        profiles = self.semantic_profile(profile)
        if profiles is not None:
            if self.structures is None:
                raise AssertionError(
                    "structured semantics must be initialized after admission"
                )
            assert profile is not None
            return profiles.binding(
                profile, sort.action, sort.side, namespace, self.structures
            )
        ports = self.input_ports(sort, namespace)
        if self.expressions.primitive(sort.action) is not None:
            return ports[0]
        if self.structures is None:
            raise AssertionError(
                "structured semantics must be initialized after admission"
            )
        if self.codecs is None:
            self.codecs = StateCodecArena(self.runtime, self.structures)
        return self.codecs.compile(sort.action, sort.side, namespace)

    @staticmethod
    def environment_ports(
        environment: tuple[
            tuple[ExprID, FinitePort | StateCodec | ReachableCodec], ...
        ],
    ) -> tuple[FinitePort, ...]:
        return tuple(
            sorted(
                (
                    port
                    for _, binding in environment
                    for port in (
                        (binding,) if isinstance(binding, FinitePort) else binding.ports
                    )
                ),
                key=lambda port: port.variable,
            )
        )

    def compile_structured(
        self,
        expression: ExprID,
        parameters: tuple[ExprID, ...] = (),
        *,
        profile: SemanticProfileID | None = None,
    ) -> CompiledStructuredExpression:
        """Enter the index's one scheduler, never a nested construction driver.

        Reachable profiles narrow *open* composed-state inputs.  A closed
        expression has no source/input binding to narrow, so profile decoding
        can only add construction work and cannot change its denotation.  Use
        the universal exact compiler for that case while retaining the caller's
        requested profile in the result metadata.
        """
        if self.runtime.semantic_compiler is not self:
            raise ValueError(
                "structured compilation requires the runtime-owned compiler"
            )
        root = self.expressions.node(expression)
        effective_profile = profile
        if profile is not None and not parameters and not root.free_ports:
            self.semantic_profile(profile)  # validate ownership before the fast path
            effective_profile = None
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_CLOSED_UNIVERSAL_COMPILATIONS
            )
        result = self.runtime.execute(
            CompileStructuredExpression(expression, parameters, effective_profile)
        )
        if type(result) is not StructureID:
            raise AssertionError("structured scheduler returned a different result")
        sorts = tuple(self.expressions.node(parameter).sort for parameter in parameters)
        if any(type(sort) is not StateSort for sort in sorts):
            raise AssertionError("admitted parameter lost its primitive state sort")
        state_sorts = tuple(sort for sort in sorts if isinstance(sort, StateSort))
        return CompiledStructuredExpression(
            result,
            self._ports_for(parameters, profile),
            state_sorts,
            root.sort,
            profile,
        )

    def validate_task(self, task: StructuredTask) -> None:
        if type(task) is CompileStructuredExpression:
            self._admit(
                task.expression, task.parameters, structured=True, profile=task.profile
            )
            return
        if type(task) is not StructuredExpressionTask:
            raise TypeError("unknown semantic expression construction task")
        self.semantic_profile(task.profile)
        if (
            type(task.depth) is not int
            or type(task.environment) is not tuple
            or not 0 <= task.depth <= len(task.environment)
        ):
            raise ValueError("invalid semantic expression binder depth")
        parameters: list[ExprID] = []
        variables: set[PortVariable] = set()
        namespaces: set[str] = set()
        for binding in task.environment:
            if type(binding) is not tuple or len(binding) != 2:
                raise ValueError("semantic environment requires expression/port pairs")
            parameter, value = binding
            node = self.expressions.node(parameter)
            if node.kind != "port" or type(node.sort) is not StateSort:
                raise ValueError("semantic environment requires state variables")
            if type(value) is FinitePort:
                FinitePort.__post_init__(value)
                if value.cardinality != self.atom_sort(node.sort).cardinality:
                    raise ValueError("semantic environment has a mismatched port")
                ports: tuple[FinitePort, ...] = (value,)
            elif type(value) is StateCodec and self.codecs is not None:
                if task.profile is not None:
                    raise ValueError(
                        "universal state codec cannot enter a reachable profile"
                    )
                self.codecs.validate_codec(value)
                if (
                    value.request.action != node.sort.action
                    or value.request.side != node.sort.side
                ):
                    raise ValueError(
                        "semantic environment codec has a different state sort"
                    )
                ports = value.ports
                namespaces.add(value.request.namespace.role)
            elif (
                type(value) is ReachableCodec
                and self.profiles is not None
                and self.structures is not None
            ):
                self.profiles.validate_codec(value, self.structures)
                if (
                    value.profile != task.profile
                    or value.request.action != node.sort.action
                    or value.request.side != node.sort.side
                ):
                    raise ValueError(
                        "reachable codec has a different profile or state sort"
                    )
                ports = value.ports
                namespaces.add(value.request.namespace.role)
            else:
                raise ValueError(
                    "semantic environment requires issued typed state encodings"
                )
            if any(port.variable in variables for port in ports):
                raise ValueError("semantic environment has duplicate ports")
            parameters.append(parameter)
            variables.update(port.variable for port in ports)
        # All storage names for the next binder are reserved, including its
        # independent function-entry ports when the binder is a paired state.
        reserved = f"semantic-lambda-{task.depth:08}"
        if reserved in namespaces or any(
            variable.role == reserved
            or variable.role.startswith(f"state-codec/{reserved}/")
            for variable in variables
        ):
            raise ValueError("semantic binder would capture an existing finite port")
        self._admit(
            task.expression, tuple(parameters), structured=True, profile=task.profile
        )

    def probe_task(self, task: StructuredTask) -> StructureID | None:
        self.validate_task(task)
        # Per-expression observed results are deliberately never memoized.
        return None

    def _output_matches(
        self,
        source: ExpressionSort,
        output: SemanticSort,
        profile: SemanticProfileID | None = None,
    ) -> bool:
        pending = [(source, output)]
        while pending:
            expected, actual = pending.pop()
            if isinstance(expected, SymbolSort):
                if actual != self.atom_sort(expected):
                    return False
            elif isinstance(expected, FunctionSort):
                domain = self.input_ports(
                    expected.domain, PortVariable(0, 0, "output-domain", 0), profile
                )
                if type(actual) is not SemanticFunctionSort or tuple(
                    port.cardinality for port in actual.inputs
                ) != tuple(port.cardinality for port in domain):
                    return False
                pending.append((expected.codomain, actual.output))
            elif self.expressions.primitive(expected.action) is not None:
                if actual != self.atom_sort(expected):
                    return False
            else:
                action = self.runtime.actions.resolve(expected.action)
                if (
                    action.kind != "compose"
                    or type(actual) is not ProductSort
                    or len(actual.items) != 2
                ):
                    return False
                first = self.runtime.actions.reference(action.first)
                second = self.runtime.actions.reference(action.second)
                pending.extend(
                    (
                        (StateSort(first, expected.side), actual.items[0]),
                        (
                            FunctionSort(
                                StateSort(first, 1 - expected.side),
                                StateSort(second, expected.side),
                            ),
                            actual.items[1],
                        ),
                    )
                )
        return True

    def publication(self, task: StructuredTask, result: Result) -> None:
        # Validate result provenance and interface before validation telemetry.
        if self.structures is None or type(result) is not StructureID:
            raise ValueError("structured publication requires a local semantic result")
        value = self.structures.resolve(result)
        self.validate_task(task)
        expected = self.expressions.node(task.expression).sort
        if isinstance(task, CompileStructuredExpression):
            ports = self._ports_for(task.parameters, task.profile)
        else:
            ports = self.environment_ports(task.environment)
        if value.signature.inputs != ports or not self._output_matches(
            expected, value.signature.output, task.profile
        ):
            raise ValueError("structured result has a different input/output interface")
        # The semantic arenas already own canonical functions. No binding from
        # this expression occurrence to its observed result is published here.

    def program(self, task: StructuredTask) -> Generator[Task, Result, Result]:
        self.validate_task(task)
        if self.structures is None:
            self.structures = StructureArena(
                BitFunctionArena(self.ledger, self.functions)
            )
        if type(task) is CompileStructuredExpression:
            environment = tuple(
                (
                    parameter,
                    self.expression_binding(
                        parameter,
                        PortVariable(0, 0, f"semantic-parameter-{index:08}", 0),
                        task.profile,
                    ),
                )
                for index, parameter in enumerate(task.parameters)
            )
            return (
                yield StructuredExpressionTask(
                    task.expression, environment, profile=task.profile
                )
            )
        assert isinstance(task, StructuredExpressionTask)
        self.ledger.bump(_interfaces_keys.SEMANTIC_STRUCTURED_EXPRESSION_TASKS)
        return (yield from self.structured_program(task, self.structures))

    def factored(
        self, function: SemanticFunctionID, bits: BitFunctionArena
    ) -> FactoredFunctionID:
        """Convert a canonical scalar function through the shared semantic cache."""
        return bits.from_scalar(function)

    def structured_program(
        self, task: StructuredExpressionTask, structures: StructureArena
    ) -> Generator[Task, Result, Result]:
        from number_compiler.hashlife.interfaces.structured_compilation import (
            structured_program,
        )

        return structured_program(self, task, structures)

    def declare_structure(
        self,
        value: StructureID,
        inputs: tuple[FinitePort, ...],
        structures: StructureArena,
    ) -> StructureID:
        return structures.declare(value, inputs)

    def encode_argument(
        self,
        sort: StateSort,
        ports: tuple[FinitePort, ...],
        argument: StructureID,
        structures: StructureArena,
        profile: SemanticProfileID | None = None,
    ) -> dict[PortVariable, FactoredFunctionID]:
        from number_compiler.hashlife.interfaces.structured_compilation import (
            encode_argument,
        )

        return encode_argument(self, sort, ports, argument, structures, profile)

    def _declare(
        self, function: SemanticFunctionID, ports: tuple[FinitePort, ...]
    ) -> SemanticFunctionID:
        node = self.functions.resolve(function)
        merged = {port.variable: port for port in node.signature.inputs}
        for port in ports:
            previous = merged.get(port.variable)
            if previous is not None and previous != port:
                raise ValueError("semantic binder has incompatible primitive domains")
            merged[port.variable] = port
        signature = FunctionSignature(
            tuple(merged[key] for key in sorted(merged)), node.signature.output
        )
        if signature == node.signature:
            return function
        transaction = _Transaction(self.functions)
        root = transaction.resign(function.local_id, signature)
        return transaction.finish(transaction.admissible(root))

    def finite_child(
        self, node: BoundaryExprNode
    ) -> tuple[SemanticFunctionID, FinitePort]:
        assert node.function is not None
        source = self.expressions.node(
            self.expressions.reference(node.children[0])
        ).sort
        assert isinstance(source, StateSort)
        return self._finite(node.function, source, node.sort)

    def _program(
        self, task: _Task
    ) -> Generator[_Task, SemanticFunctionID, SemanticFunctionID]:
        arena = self.expressions
        node = arena.node(task.expression)
        if node.kind in ("call", "anchor", "continuation"):
            head = self.runtime.execute(ResolveExpr(task.expression))
            if type(head) is not ExprID or head == task.expression:
                raise UnsupportedInterfaceError(
                    "structured expression has no constructor head"
                )
            return (yield _Task(head, task.environment, task.depth))
        if node.kind == "port":
            port = dict(task.environment).get(task.expression)
            if port is None:
                raise ValueError("unbound semantic port")
            return self.functions.variable((port,), port, self.atom_sort(node.sort))
        if node.kind in ("literal", "symbol"):
            return self.functions.atom(
                FunctionSignature((), self.atom_sort(node.sort)), node.value
            )
        if node.kind == "lambda":
            assert isinstance(node.sort, FunctionSort)
            domain = self.atom_sort(node.sort.domain)
            variable = arena.fresh_variable(
                node.sort.domain,
                "semantic-bound-input",
                (task.expression,) + tuple(item[0] for item in task.environment),
            )
            port = FinitePort(
                PortVariable(0, 0, f"semantic-lambda-{task.depth:08}", 0),
                domain.cardinality,
            )
            body = arena.apply(task.expression, variable)
            function = yield _Task(
                body, task.environment + ((variable, port),), task.depth + 1
            )
            return self.functions.curry(self._declare(function, (port,)), (port,))
        children: list[SemanticFunctionID] = []
        for child in node.children:
            children.append(
                (yield _Task(arena.reference(child), task.environment, task.depth))
            )
        if node.kind == "pair":
            return self.functions.product(tuple(children))
        if node.kind == "apply":
            target = self.functions.resolve(children[0]).signature.output
            if not isinstance(target, SemanticFunctionSort) or len(target.inputs) != 1:
                raise UnsupportedInterfaceError(
                    "application needs one primitive semantic input"
                )
            return self.functions.apply(
                children[0], {target.inputs[0].variable: children[1]}
            )
        if node.kind in ("finite_apply", "finite_map"):
            mapped, port = self.finite_child(node)
            return self.functions.substitute(mapped, {port.variable: children[0]})
        if node.kind in ("advance", "emit") and node.action is not None:
            primitive = self.primitives.compile(
                self.runtime.actions.primitive(node.action)
            )
            zero_left = self.functions.atom(
                FunctionSignature((), primitive.left_sort), 0
            )
            zero_right = self.functions.atom(
                FunctionSignature((), primitive.right_sort), 0
            )
            function, arguments = primitive_operation(
                primitive, node.kind, node.side, tuple(children), zero_left, zero_right
            )
            return self.functions.substitute(
                function,
                dict(
                    zip(
                        (port.variable for port in primitive.ports),
                        arguments,
                        strict=True,
                    )
                ),
            )
        raise UnsupportedInterfaceError(
            f"unsupported semantic expression constructor: {node.kind}"
        )

    def _finite(
        self, reference: object, source: StateSort, target: ExpressionSort
    ) -> tuple[SemanticFunctionID, FinitePort]:
        if type(reference) is not TransferSummaryID:
            raise ValueError("finite map needs an actual function ID")
        self.runtime.kernels.expression(reference)
        domain = self.atom_sort(source).cardinality
        port = FinitePort(PortVariable(0, 0, "semantic-finite-map-input", 0), domain)
        signature = FunctionSignature((port,), self.atom_sort(target))
        key = FiniteLiftKey(reference, source, target)
        self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_REQUESTS)
        cached = self._finite_lifts.get(key)
        if cached is not None:
            function, cached_port = cached
            self.functions.resolve(function)
            FinitePort.__post_init__(cached_port)
            if (
                cached_port != port
                or self.functions.resolve(function).signature != signature
            ):
                raise ValueError("cached finite lift has another complete interface")
            self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_HITS)
            return cached
        original = LEFT_A if source.side == 0 else RIGHT_A
        transaction = _Transaction(self.functions)
        pending = [(0, 0, False)]
        results: list[int] = []
        while pending:
            bit, value, ready = pending.pop()
            self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_FRAMES)
            if ready:
                high, low = results.pop(), results.pop()
                variable = PortVariable(0, 0, port.variable.role, bit)
                results.append(transaction.decision(signature, variable, low, high))
            elif bit == port.bits:
                if value >= domain:
                    terminal = SemanticTerminal("invalid")
                else:
                    output = self.runtime.kernels.evaluate(
                        reference, observation_inputs(domain, original, value)
                    )
                    terminal = SemanticTerminal("atom", output)
                results.append(transaction.terminal(signature, terminal))
            else:
                defer_indexed_dependencies(
                    pending,
                    bit,
                    value,
                    ((bit + 1, value), (bit + 1, value | (1 << bit))),
                    (),
                )

        from number_compiler.hashlife.interfaces.semantic_publication import (
            prepare_functions,
        )

        prepared = None
        try:
            prepared = prepare_functions(transaction, (results[0],))
            prepared.reserve_with(((self._finite_lifts.owner, 1, 0),))
            prepared.publish_reserved()
            result = prepared.roots[0], port
            self._finite_lifts.publish_reserved(key, result)
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_EVALUATIONS
            )
            return result
        finally:
            if prepared is None:
                transaction.close()
            else:
                prepared.cancel()
