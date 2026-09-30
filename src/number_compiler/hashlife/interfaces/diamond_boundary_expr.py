"""Typed parametric boundary programs; higher interfaces remain structured.

Lambda bodies use de Bruijn indices. Public handles denote expressions closed
with respect to binders (free named ports are permitted). Programs are reduced
syntactically, not claimed to be an extensional quotient of higher functions.
"""

from __future__ import annotations

from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    evaluate_primitive_bits,
)

from collections.abc import Mapping, MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal, TypeAlias

from number_compiler.arithmetic.contracts.block_effect import BoundarySide, _effect_key
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryStateID,
)
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    input_expression,
)
from number_compiler.hashlife.interfaces.diamond_unary import PrimitiveUnaryFunctions
from number_compiler.hashlife.interfaces.expression_transactions import _Transaction

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
        ClosureProgramID,
    )


@dataclass(frozen=True, slots=True)
class ExprID(ArenaHandle):
    pass


@dataclass(frozen=True, slots=True)
class StateSort:
    action: ActionProgramID
    side: int


@dataclass(frozen=True, slots=True)
class FunctionSort:
    domain: StateSort
    codomain: StateSort


@dataclass(frozen=True, slots=True)
class SymbolSort:
    base: int
    blank: int


ExpressionSort: TypeAlias = StateSort | FunctionSort | SymbolSort
ExpressionKind: TypeAlias = Literal[
    "port",
    "bound",
    "literal",
    "symbol",
    "pair",
    "anchor",
    "continuation",
    "lambda",
    "apply",
    "advance",
    "emit",
    "finite_apply",
    "finite_map",
    "call",
]


@dataclass(frozen=True, slots=True)
class FormalPort:
    sort: ExpressionSort
    role: str


def _port_order(port: FormalPort) -> tuple[str, int, int, int, int, str]:
    sort = port.sort
    if type(sort) is StateSort:
        return ("state", sort.action.local_id, sort.side, 0, 0, port.role)
    if type(sort) is FunctionSort:
        return (
            "function",
            sort.domain.action.local_id,
            sort.domain.side,
            sort.codomain.action.local_id,
            sort.codomain.side,
            port.role,
        )
    if type(sort) is SymbolSort:
        return ("symbol", sort.base, sort.blank, 0, 0, port.role)
    raise ValueError("unknown formal port sort")


@dataclass(frozen=True, slots=True)
class BoundaryExprNode:
    kind: ExpressionKind
    sort: ExpressionSort
    children: tuple[int, ...] = ()
    role: str = ""
    bound: int = -1
    state: BoundaryStateID | None = None
    value: int = -1
    action: ActionProgramID | None = None
    side: int = -1
    scope: int = 0
    free_ports: tuple[FormalPort, ...] = ()
    function: TransferSummaryID | None = None
    closure: ClosureProgramID | None = None
    binding_safe: bool = False


@dataclass(frozen=True, slots=True)
class ExprBinding:
    variable: ExprID
    value: ExprID


@dataclass(frozen=True, slots=True)
class ExprSubstitutionKey:
    expression: ExprID
    bindings: tuple[ExprBinding, ...]


_Mode: TypeAlias = Literal["normal", "free", "abstract", "beta", "shift"]


@dataclass(frozen=True, slots=True)
class _Rewrite:
    mode: _Mode
    root: int
    depth: int = 0
    parameter: int = 0


class BoundaryExpressionArena:
    def __init__(
        self,
        boundaries: BoundaryActionArena,
        *,
        unary: PrimitiveUnaryFunctions | None = None,
    ) -> None:
        if unary is not None and unary.kernels is not boundaries.kernels:
            raise ValueError("unary functions belong to another kernel arena")
        self.boundaries = boundaries
        self.unary = (
            PrimitiveUnaryFunctions(boundaries.kernels) if unary is None else unary
        )
        self.actions = boundaries.temporals
        self.ledger = boundaries.ledger
        self.token = ArenaToken("diamond-boundary-expressions")
        self.ledger.register_execution_root(self)
        prefix = f"diamond-boundary-expressions-{len(self.ledger.inventory())}"
        self.node_owner = self.ledger.register(
            prefix + "-nodes", "boundary_expression_program"
        )
        self.key_owner = self.ledger.register(
            prefix + "-keys", "boundary_expression_interner"
        )
        self.memo_owner = self.ledger.register(prefix + "-substitution", "query_memo")
        self.nodes: MutableSequence[BoundaryExprNode] = self.ledger.make_list(
            self.node_owner
        )
        self.keys: MutableMapping[BoundaryExprNode, ExprID] = self.ledger.make_dict(
            self.key_owner
        )
        self.memo: MutableMapping[ExprSubstitutionKey, ExprID] = self.ledger.make_dict(
            self.memo_owner
        )
        self.ledger.register_container(
            self.memo_owner,
            self.memo,
            node_count=lambda: 0,
            payloads=lambda: self.memo.items(),
            evict=self.clear,
            composition_count=lambda: len(self.memo),
        )
        from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
            ExpressionClosures,
        )

        self.closures = ExpressionClosures(self)

    def clear(self) -> None:
        count = len(self.memo)
        self.memo.clear()
        self.ledger.release(self.memo_owner, entries=count)

    def _handle(self, index: int) -> ExprID:
        return ExprID(self.token, "diamond-boundary-expression", index)

    def _resolve(self, expression: ExprID) -> int:
        if type(expression) is not ExprID:
            raise ValueError("expected a typed boundary expression")
        expression.validate(
            self.token, "diamond-boundary-expression", size=len(self.nodes)
        )
        if self.nodes[expression.local_id].scope:
            raise ValueError("a bound expression cannot escape its lambda")
        return expression.local_id

    def node(self, expression: ExprID) -> BoundaryExprNode:
        return self.nodes[self._resolve(expression)]

    def _validate_sort(self, sort: ExpressionSort) -> None:
        if type(sort) is StateSort:
            self.actions.resolve(sort.action)
            if type(sort.side) is not int or sort.side not in (0, 1):
                raise ValueError("invalid state direction")
        elif type(sort) is SymbolSort:
            if (
                type(sort.base) is not int
                or sort.base < 2
                or type(sort.blank) is not int
                or not 1 <= sort.blank < 1 << 64
            ):
                raise ValueError("invalid symbol alphabet")
        elif type(sort) is FunctionSort:
            # The finite nesting depth is fixed by this schema, not a recursive
            # higher-order Cartesian domain.
            if (
                type(sort.domain) is not StateSort
                or type(sort.codomain) is not StateSort
            ):
                raise ValueError("continuations map state sorts to state sorts")
            for state in (sort.domain, sort.codomain):
                self.actions.resolve(state.action)
                if type(state.side) is not int or state.side not in (0, 1):
                    raise ValueError("invalid continuation direction")
            first, second = (
                self.actions.resolve(sort.domain.action),
                self.actions.resolve(sort.codomain.action),
            )
            if (
                first.kind != "identity"
                and second.kind != "identity"
                and (first.base, first.blank) != (second.base, second.blank)
            ):
                raise ValueError("incompatible continuation alphabets")
        else:
            raise ValueError("unknown boundary expression sort")

    def state_sort(self, action: ActionProgramID, side: int) -> StateSort:
        sort = StateSort(action, side)
        self._validate_sort(sort)
        return sort

    def function_sort(self, domain: StateSort, codomain: StateSort) -> FunctionSort:
        sort = FunctionSort(domain, codomain)
        self._validate_sort(sort)
        return sort

    def symbol_sort(self, action: ActionProgramID) -> SymbolSort:
        node = self.actions.resolve(action)
        if node.kind == "identity":
            original = self.boundaries.cells.source_geometry._construction.source
            return SymbolSort(original.base, original.blank)
        return SymbolSort(node.base, node.blank)

    def primitive(self, action: ActionProgramID) -> PrimitiveKernel | None:
        """Read an already admitted immutable kernel; never allocate one."""
        if self.actions.resolve(action).kind != "atom":
            return None
        handle = self.boundaries.kernels._kernel_ids.get(
            _effect_key(self.actions.primitive(action))
        )
        return None if handle is None else self.boundaries.kernels.kernel(handle)

    def _finish(self, node: BoundaryExprNode) -> ExprID:
        transaction = _Transaction(self)
        reduced = transaction.reduce(node)
        root = reduced if isinstance(reduced, int) else transaction.rewrite(reduced)
        return transaction.publish(root)

    def variable(self, sort: ExpressionSort, role: str) -> ExprID:
        self._validate_sort(sort)
        if type(role) is not str or not role:
            raise ValueError("formal ports require a stable nonempty role")
        return self._finish(BoundaryExprNode("port", sort, role=role))

    def fresh_variable(
        self, sort: ExpressionSort, role: str, avoid: Sequence[ExprID]
    ) -> ExprID:
        """Choose a binder name fresh for every declared incoming expression.

        The least unused role suffix is stable across repeated requests; lambda
        abstraction removes it into a de Bruijn index before function interning.
        All expressions contributing free ports to the new body belong in avoid.
        """
        self._validate_sort(sort)
        if type(role) is not str or not role:
            raise ValueError("formal ports require a stable nonempty role")
        roots = [self._resolve(expression) for expression in avoid]
        used = {
            port.role
            for root in roots
            for port in self.nodes[root].free_ports
            if port.sort == sort
        }
        self.ledger.bump("boundary_expression_freshness_root_queries", len(roots))
        self.ledger.bump(
            "boundary_expression_freshness_port_visits",
            sum(len(self.nodes[root].free_ports) for root in roots),
        )
        candidate = role
        suffix = 0
        while candidate in used:
            suffix += 1
            candidate = f"{role}:{suffix}"
        return self.variable(sort, candidate)

    def literal(self, state: BoundaryStateID) -> ExprID:
        node = self.boundaries.state(state)
        sort = self.state_sort(node.action, node.side)
        if node.literal < 0 or self.actions.resolve(node.action).kind == "compose":
            raise ValueError("only finite primitive boundary literals are admitted")
        primitive = self.primitive(node.action)
        size = (
            1
            if self.actions.resolve(node.action).kind == "identity"
            else (
                None
                if primitive is None
                else len(primitive.domain(BoundarySide(node.side)))
            )
        )
        if (
            size is None
            or type(node.literal) is not int
            or not 0 <= node.literal < size
        ):
            raise ValueError(
                "finite literal requires an already admitted primitive domain"
            )
        return self._finish(BoundaryExprNode("literal", sort, value=node.literal))

    def symbol(self, action: ActionProgramID, value: int) -> ExprID:
        sort = self.symbol_sort(action)
        if type(value) is not int or not 0 <= value <= sort.blank:
            raise ValueError("symbol is outside the original kernel alphabet")
        return self._finish(BoundaryExprNode("symbol", sort, value=value))

    def _pair_sorts(
        self, action: ActionProgramID, side: int
    ) -> tuple[StateSort, FunctionSort]:
        self.state_sort(action, side)
        node = self.actions.resolve(action)
        if node.kind != "compose":
            raise ValueError("pair ports require a composed action")
        first, second = (
            self.actions._handle(node.left),
            self.actions._handle(node.right),
        )
        return StateSort(first, side), FunctionSort(
            StateSort(first, 1 - side), StateSort(second, side)
        )

    def pair(
        self, action: ActionProgramID, side: int, anchor: ExprID, continuation: ExprID
    ) -> ExprID:
        left, right = self._resolve(anchor), self._resolve(continuation)
        anchor_sort, function_sort = self._pair_sorts(action, side)
        if (
            self.nodes[left].sort != anchor_sort
            or self.nodes[right].sort != function_sort
        ):
            raise ValueError("pair expression has incompatible component sorts")
        return self._finish(
            BoundaryExprNode("pair", StateSort(action, side), (left, right))
        )

    def anchor(self, expression: ExprID) -> ExprID:
        root = self._resolve(expression)
        sort = self.nodes[root].sort
        if type(sort) is not StateSort:
            raise ValueError("anchor requires a structured state")
        anchor_sort, _ = self._pair_sorts(sort.action, sort.side)
        return self._finish(BoundaryExprNode("anchor", anchor_sort, (root,)))

    def continuation(self, expression: ExprID) -> ExprID:
        root = self._resolve(expression)
        sort = self.nodes[root].sort
        if type(sort) is not StateSort:
            raise ValueError("continuation requires a structured state")
        _, function_sort = self._pair_sorts(sort.action, sort.side)
        return self._finish(BoundaryExprNode("continuation", function_sort, (root,)))

    def lambda_(self, variable: ExprID, body: ExprID) -> ExprID:
        argument, root = self._resolve(variable), self._resolve(body)
        domain, codomain = self.nodes[argument].sort, self.nodes[root].sort
        if (
            self.nodes[argument].kind != "port"
            or type(domain) is not StateSort
            or type(codomain) is not StateSort
        ):
            raise ValueError("lambda requires a state port and a state body")
        sort = self.function_sort(domain, codomain)
        transaction = _Transaction(self)
        abstracted = transaction.rewrite(_Rewrite("abstract", root, parameter=argument))
        reduced = transaction.reduce(BoundaryExprNode("lambda", sort, (abstracted,)))
        result = reduced if isinstance(reduced, int) else transaction.rewrite(reduced)
        return transaction.publish(result)

    def apply(self, function: ExprID, argument: ExprID) -> ExprID:
        first, second = self._resolve(function), self._resolve(argument)
        sort = self.nodes[first].sort
        if type(sort) is not FunctionSort or self.nodes[second].sort != sort.domain:
            raise ValueError("continuation application has an incompatible input")
        return self._finish(BoundaryExprNode("apply", sort.codomain, (first, second)))

    def constant_function(self, function: ExprID) -> ExprID | None:
        """Probe a complete function before scheduling an unused argument.

        A closed lambda body has no reference to its argument, including below
        nested binders. This is a read-only syntactic proof, not a sample.
        """
        root = self._resolve(function)
        node = self.nodes[root]
        if type(node.sort) is not FunctionSort:
            raise ValueError("constant-function probe requires a function")
        if node.kind == "lambda" and self.nodes[node.children[0]].scope == 0:
            return self._handle(node.children[0])
        return None

    def call(self, program: ClosureProgramID, arguments: Sequence[ExprID]) -> ExprID:
        effective = self.closures.effective_arguments(program, arguments)
        sort = self.closures.result_sort(program)
        children = tuple(self._resolve(argument) for argument in effective)
        return self._finish(BoundaryExprNode("call", sort, children, closure=program))

    def expand_call(self, expression: ExprID) -> ExprID:
        node = self.node(expression)
        if node.kind != "call" or node.closure is None:
            raise ValueError("explicit expansion requires a closure call")
        return self.closures.expand(
            node.closure, tuple(self._handle(child) for child in node.children)
        )

    def finite_apply(
        self,
        action: ActionProgramID,
        side: int,
        summary: TransferSummaryID,
        argument: ExprID,
    ) -> ExprID:
        """Apply a complete one-primitive-port function to a symbolic state."""
        root = self._resolve(argument)
        sort = self.state_sort(action, side)
        expression = self.boundaries.kernels.expression(summary)
        primitive = self.primitive(action)
        if primitive is None or self.nodes[root].sort != sort:
            raise ValueError(
                "finite application requires an admitted matching primitive state"
            )
        domain = len(primitive.domain(BoundarySide(side)))
        if expression.domain != domain:
            raise ValueError("finite function has another primitive codomain")
        port = LEFT_A if side == 0 else RIGHT_A
        width = (domain - 1).bit_length()
        allowed = {
            PortVariable(port.time, port.side, port.role, port.bit + bit)
            for bit in range(width)
        }
        functions = self.boundaries.kernels.functions
        pending = list(expression.bits)
        checked: set[TransferSummaryID] = set()
        visits = 0
        while pending:
            bit = pending.pop()
            visits += 1
            if bit in checked:
                continue
            checked.add(bit)
            decision = functions._nodes[functions._resolve(bit)]
            if decision.variable is not None:
                if decision.variable not in allowed:
                    raise ValueError(
                        "finite function contains another primitive input port"
                    )
                pending.extend(
                    (functions._handle(decision.low), functions._handle(decision.high))
                )
        # Validate the codomain on every original primitive input, not a higher
        # Cartesian domain. This read-only check cannot publish a malformed map.
        reads = 0
        identity = constant = True
        constant_value = -1
        noncanonical = False
        for code in range(1 << width):
            output, decision_reads = evaluate_primitive_bits(
                self.boundaries.kernels, expression, code, width, port
            )
            reads += decision_reads
            if code >= domain:
                noncanonical |= output != 0
                continue
            if output >= domain:
                raise ValueError("finite function emits outside its primitive codomain")
            identity &= output == code
            if constant_value < 0:
                constant_value = output
            constant &= output == constant_value
        self.ledger.bump("boundary_expression_finite_admission_visits", visits)
        self.ledger.bump("boundary_expression_finite_admission_value_visits", reads)
        if identity:
            self.ledger.bump("boundary_expression_identity_function_early_hits")
            return argument
        if constant:
            self.ledger.bump("boundary_expression_constant_function_early_hits")
            return self._finish(BoundaryExprNode("literal", sort, value=constant_value))
        if noncanonical:
            identity_function = input_expression(self.boundaries.kernels, domain, port)
            handle = self.boundaries.kernels._kernel_ids[
                _effect_key(self.actions.primitive(action))
            ]
            summary = self.unary.compose(handle, side, summary, identity_function, port)
            self.ledger.bump("boundary_expression_finite_admissibility_normalizations")
        return self._finish(
            BoundaryExprNode("finite_apply", sort, (root,), function=summary)
        )

    def primitive_advance(
        self, action: ActionProgramID, side: int, state: ExprID, symbol: ExprID
    ) -> ExprID:
        state_id, symbol_id = self._resolve(state), self._resolve(symbol)
        sort = self.state_sort(action, side)
        if self.actions.resolve(action).kind != "atom":
            raise ValueError("primitive advance requires an atomic action")
        if self.nodes[state_id].sort != sort or self.nodes[
            symbol_id
        ].sort != self.symbol_sort(action):
            raise ValueError("primitive advance argument sorts disagree")
        return self._finish(
            BoundaryExprNode(
                "advance", sort, (state_id, symbol_id), action=action, side=side
            )
        )

    def finite_map(
        self,
        source: StateSort,
        target: StateSort,
        summary: TransferSummaryID,
        argument: ExprID,
    ) -> ExprID:
        """Apply a complete fixed-domain map, including cross-side continuations."""
        from number_compiler.hashlife.interfaces.diamond_finite_map import admit_map

        root = self._resolve(argument)
        self._validate_sort(source)
        self._validate_sort(target)
        if self.nodes[root].sort != source:
            raise ValueError("finite map argument has another primitive port sort")
        function, constant, identity = admit_map(self, source, target, summary)
        if identity:
            self.ledger.bump("boundary_expression_identity_function_early_hits")
            return argument
        if constant is not None:
            self.ledger.bump("boundary_expression_constant_function_early_hits")
            return self._finish(BoundaryExprNode("literal", target, value=constant))
        return self._finish(
            BoundaryExprNode("finite_map", target, (root,), function=function)
        )

    def primitive_emit(
        self, action: ActionProgramID, left: ExprID, symbol: ExprID, right: ExprID
    ) -> ExprID:
        left_id, symbol_id, right_id = (
            self._resolve(left),
            self._resolve(symbol),
            self._resolve(right),
        )
        if self.actions.resolve(action).kind != "atom":
            raise ValueError("primitive emit requires an atomic action")
        sort = self.symbol_sort(action)
        if (
            self.nodes[left_id].sort != StateSort(action, 0)
            or self.nodes[right_id].sort != StateSort(action, 1)
            or self.nodes[symbol_id].sort != sort
        ):
            raise ValueError("primitive emit argument sorts disagree")
        return self._finish(
            BoundaryExprNode(
                "emit", sort, (left_id, symbol_id, right_id), action=action
            )
        )

    def substitute(
        self, expression: ExprID, substitutions: Mapping[ExprID, ExprID]
    ) -> ExprID:
        root = self._resolve(expression)
        admitted: dict[int, int] = {}
        for variable, value in substitutions.items():
            port, replacement = self._resolve(variable), self._resolve(value)
            if (
                self.nodes[port].kind != "port"
                or self.nodes[port].sort != self.nodes[replacement].sort
            ):
                raise ValueError("substitution requires equal-sort formal ports")
            if port != replacement:
                admitted[port] = replacement
        # The exact derived support is part of each immutable program node.
        # It names declared symbolic ports, never spatial coordinates or values.
        support = set(self.nodes[root].free_ports)
        effective = {
            port
            for port in admitted
            if FormalPort(self.nodes[port].sort, self.nodes[port].role) in support
        }
        self.ledger.bump("boundary_expression_support_metadata_queries")
        self.ledger.bump("boundary_expression_support_port_visits", len(support))
        self.ledger.bump("boundary_expression_substitution_requests")
        if not effective:
            self.ledger.bump("boundary_expression_substitution_direct_results")
            return expression
        bindings = tuple(
            ExprBinding(self._handle(port), self._handle(admitted[port]))
            for port in sorted(effective)
        )
        key = ExprSubstitutionKey(expression, bindings)
        found = self.memo.get(key)
        if found is not None:
            self.ledger.bump("boundary_expression_substitution_cache_hits")
            return found
        self.ledger.bump("boundary_expression_substitution_evaluations")
        transaction = _Transaction(self)
        transaction.substitutions = {port: admitted[port] for port in effective}
        transaction.substitution_ports = frozenset(
            FormalPort(self.nodes[port].sort, self.nodes[port].role)
            for port in effective
        )
        result = transaction.rewrite(_Rewrite("free", root))
        return transaction.publish(result, key)
