"""Independent, per-snapshot typing audit for structured boundary programs."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgram,
    ClosureProgramID,
    ExpressionClosures,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
    ResolveExpr,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    BoundaryExprNode,
    ExprBinding,
    ExprID,
    ExprSubstitutionKey,
    FormalPort,
    FunctionSort,
    StateSort,
    SymbolSort,
    _port_order,
)
from number_compiler.resources.ledger import ResourceLedger


def _integer(value: object, lower: int = 0) -> bool:
    return type(value) is int and value >= lower


class ExpressionPayloadRegistry:
    """Inspect stored children and binder requirements without rewriting them.

    Child IDs must be topological. Binder requirement maps are temporary audit
    metadata and prove both the declared scope and the sort of every bound use.
    """

    record_types = (
        ExprID,
        StateSort,
        FunctionSort,
        SymbolSort,
        FormalPort,
        BoundaryExprNode,
        ExprBinding,
        ExprSubstitutionKey,
        ClosureProgram,
        ClosureProgramID,
        ResolveExpr,
        LowerFinite,
    )

    def __init__(
        self,
        ledger: ResourceLedger,
        action_valid: Callable[[object], bool],
        boundary_valid: Callable[[object], bool],
    ) -> None:
        self.action_valid, self.boundary_valid = action_valid, boundary_valid
        actual = dict(ledger.iter_containers())
        self.arenas = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is BoundaryExpressionArena
            and root.ledger is ledger
            and actual.get(root.node_owner) is root.nodes
            and actual.get(root.key_owner) is root.keys
            and actual.get(root.memo_owner) is root.memo
        )
        self.closures = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is ExpressionClosures
            and root.ledger is ledger
            and root.expressions in self.arenas
            and actual.get(root.node_owner) is root.nodes
            and actual.get(root.id_owner) is root.ids
        )
        self.closure_records = {
            id(record): root for root in self.closures for record in root.nodes
        }
        self.records: dict[int, bool] = {}
        self.finite_checks: dict[
            tuple[object, StateSort, StateSort | SymbolSort, TransferSummaryID, bool],
            bool,
        ] = {}
        self.valid_nodes: dict[object, tuple[bool, ...]] = {}
        self.realized_nodes: dict[object, tuple[bool, ...]] = {}
        self.universal_program_nodes: dict[object, tuple[bool, ...]] = {}
        for arena in self.arenas:
            checks: list[bool] = []
            realized: list[bool] = []
            universal: list[bool] = []
            requirements: list[dict[int, StateSort]] = []
            for index, node in enumerate(arena.nodes):
                valid, needed = self._node(arena, index, node, checks, requirements)
                safe = self._universal_node(arena, node, valid, universal)
                valid = (
                    valid
                    and type(node.binding_safe) is bool
                    and node.binding_safe == safe
                )
                checks.append(valid)
                requirements.append(needed)
                self.records[id(node)] = valid
                realized.append(
                    valid
                    and type(node) is BoundaryExprNode
                    and node.kind in ("literal", "symbol", "pair", "lambda", "bound")
                    and all(realized[child] for child in node.children)
                )
                universal.append(safe and valid)
            self.valid_nodes[arena.token] = tuple(checks)
            self.realized_nodes[arena.token] = tuple(realized)
            self.universal_program_nodes[arena.token] = tuple(universal)
        self.invalid_response_objects: set[tuple[int, int]] = set()
        for arena in self.arenas:
            for key, result in arena.memo.items():
                if not self._memo_entry(arena, key, result):
                    self.invalid_response_objects.update(
                        ((arena.memo_owner, id(key)), (arena.memo_owner, id(result)))
                    )

    @staticmethod
    def _universal_node(
        arena: BoundaryExpressionArena, node: object, valid: bool, prior: list[bool]
    ) -> bool:
        if not valid or type(node) is not BoundaryExprNode:
            return False
        if (
            not node.free_ports
            and not node.scope
            and node.kind
            not in ("literal", "symbol", "port", "bound", "lambda", "pair")
            and not (
                node.kind in ("finite_apply", "finite_map")
                and len(node.children) == 1
                and arena.nodes[node.children[0]].kind == "literal"
            )
        ):
            return False
        if not all(prior[child] for child in node.children):
            return False
        if node.kind == "call":
            assert node.closure is not None
            # _node already independently validated ownership, body ordering,
            # and all closure fields; include the opaque body in this proof.
            body = arena.closures.nodes[node.closure.local_id].body
            return prior[body.local_id]
        return True

    def universal_program(self, value: ExprID) -> bool:
        return (
            self.handle(value, closed=True)
            and self.universal_program_nodes[value.owner][value.local_id]
        )

    def response_allowed(
        self, arena: BoundaryExpressionArena, result: object, inputs: tuple[ExprID, ...]
    ) -> bool:
        if (
            type(result) is not ExprID
            or result.owner is not arena.token
            or not self.handle(result, closed=True)
        ):
            return False
        bound = False
        unsafe = False
        for value in inputs:
            if type(value) is not ExprID or value.owner is not arena.token:
                return False
            node = self.expression(value)
            if node is None:
                return False
            unsafe |= not self.universal_program_nodes[arena.token][value.local_id]
            if node.free_ports or node.kind in ("literal", "symbol"):
                continue
            if (
                node.kind in ("finite_apply", "finite_map")
                and node.function is not None
                and len(node.children) == 1
                and arena.nodes[node.children[0]].kind == "literal"
            ):
                continue
            bound = True
        if unsafe and self.universal_program_nodes[arena.token][result.local_id]:
            return False
        return not (bound and self.realized_nodes[arena.token][result.local_id])

    def _memo_entry(
        self, arena: BoundaryExpressionArena, key: object, result: object
    ) -> bool:
        if (
            type(key) is not ExprSubstitutionKey
            or not self.valid(key)
            or type(result) is not ExprID
        ):
            return False
        if key.expression.owner is not arena.token:
            return False
        first, second = self.expression(key.expression), self.expression(result)
        return (
            first is not None
            and second is not None
            and first.sort == second.sort
            and self.response_allowed(
                arena, result, tuple(binding.value for binding in key.bindings)
            )
        )

    def _state_sort(
        self, value: StateSort, arena: BoundaryExpressionArena | None
    ) -> bool:
        return (
            type(value.action) is ActionProgramID
            and self.action_valid(value.action)
            and type(value.side) is int
            and value.side in (0, 1)
            and (arena is None or value.action.owner is arena.actions.token)
        )

    def sort(self, value: object, arena: BoundaryExpressionArena | None = None) -> bool:
        if type(value) is StateSort:
            return self._state_sort(value, arena)
        if type(value) is SymbolSort:
            if not (
                _integer(value.base, 2)
                and _integer(value.blank, 1)
                and value.blank < 1 << 64
            ):
                return False
            arenas = self.arenas if arena is None else (arena,)
            return any(
                any(
                    node.kind != "identity"
                    and (node.base, node.blank) == (value.base, value.blank)
                    for node in scope.actions._nodes
                )
                for scope in arenas
            )
        if type(value) is FunctionSort:
            if (
                type(value.domain) is not StateSort
                or type(value.codomain) is not StateSort
            ):
                return False
            if not self._state_sort(value.domain, arena) or not self._state_sort(
                value.codomain, arena
            ):
                return False
            if value.domain.action.owner is not value.codomain.action.owner:
                return False
            for scope in self.arenas:
                if value.domain.action.owner is scope.actions.token:
                    first, second = (
                        scope.actions.node(value.domain.action),
                        scope.actions.node(value.codomain.action),
                    )
                    return (
                        first.kind == "identity"
                        or second.kind == "identity"
                        or (first.base, first.blank) == (second.base, second.blank)
                    )
        return False

    def handle(self, value: object, *, closed: bool = False) -> bool:
        if (
            type(value) is not ExprID
            or value.kind != "diamond-boundary-expression"
            or not _integer(value.local_id)
        ):
            return False
        for arena in self.arenas:
            if value.owner is arena.token and value.local_id < len(arena.nodes):
                return self.valid_nodes[arena.token][value.local_id] and (
                    not closed or arena.nodes[value.local_id].scope == 0
                )
        return False

    def expression(self, value: ExprID) -> BoundaryExprNode | None:
        if not self.handle(value, closed=True):
            return None
        return next(
            arena.nodes[value.local_id]
            for arena in self.arenas
            if value.owner is arena.token
        )

    def _node(
        self,
        arena: BoundaryExpressionArena,
        index: int,
        node: object,
        checks: list[bool],
        requirements: list[dict[int, StateSort]],
    ) -> tuple[bool, dict[int, StateSort]]:
        if type(node) is not BoundaryExprNode or not self.sort(node.sort, arena):
            return False, {}
        if (
            type(node.children) is not tuple
            or any(
                not _integer(child) or child >= index or not checks[child]
                for child in node.children
            )
            or not _integer(node.scope)
            or type(node.role) is not str
            or type(node.bound) is not int
            or type(node.value) is not int
            or type(node.side) is not int
        ):
            return False, {}
        if (
            node.kind != "port"
            and node.role != ""
            or node.kind != "bound"
            and node.bound != -1
            or node.state is not None
            or node.kind not in ("literal", "symbol")
            and node.value != -1
            or node.kind not in ("advance", "emit")
            and node.action is not None
            or node.kind != "advance"
            and node.side != -1
            or node.kind not in ("finite_apply", "finite_map")
            and node.function is not None
            or node.kind != "call"
            and node.closure is not None
        ):
            return False, {}
        if type(node.free_ports) is not tuple or any(
            type(port) is not FormalPort
            or not self.sort(port.sort, arena)
            or type(port.role) is not str
            or not port.role
            for port in node.free_ports
        ):
            return False, {}
        children = tuple(arena.nodes[child] for child in node.children)
        expected_ports = (
            (FormalPort(node.sort, node.role),)
            if node.kind == "port"
            else tuple(
                sorted(
                    {port for child in children for port in child.free_ports},
                    key=_port_order,
                )
            )
        )
        if node.free_ports != expected_ports:
            return False, {}
        sorts = tuple(child.sort for child in children)
        valid = False
        needed: dict[int, StateSort] = {}
        for child in node.children:
            for depth, sort in requirements[child].items():
                if depth in needed and needed[depth] != sort:
                    return False, {}
                needed[depth] = sort
        if node.kind == "port":
            valid = not children and bool(node.role)
        elif node.kind == "bound":
            valid = not children and type(node.sort) is StateSort and node.bound >= 0
            if valid and isinstance(node.sort, StateSort):
                needed = {node.bound: node.sort}
        elif node.kind == "literal" and type(node.sort) is StateSort:
            action = arena.actions.node(node.sort.action)
            kernel = arena.primitive(node.sort.action)
            domain = (
                1
                if action.kind == "identity"
                else (
                    (kernel.left_count if node.sort.side == 0 else kernel.right_count)
                    if kernel is not None
                    else 0
                )
            )
            valid = not children and node.state is None and 0 <= node.value < domain
        elif node.kind == "symbol":
            valid = (
                not children
                and type(node.sort) is SymbolSort
                and 0 <= node.value <= node.sort.blank
            )
        elif node.kind == "pair" and type(node.sort) is StateSort:
            action = arena.actions.node(node.sort.action)
            if action.kind == "compose":
                first, second = (
                    arena.actions.reference(action.first),
                    arena.actions.reference(action.second),
                )
                valid = sorts == (
                    StateSort(first, node.sort.side),
                    FunctionSort(
                        StateSort(first, 1 - node.sort.side),
                        StateSort(second, node.sort.side),
                    ),
                )
        elif (
            node.kind in ("anchor", "continuation")
            and len(children) == 1
            and type(sorts[0]) is StateSort
        ):
            source = sorts[0]
            action = arena.actions.node(source.action)
            if action.kind == "compose":
                first, second = (
                    arena.actions.reference(action.first),
                    arena.actions.reference(action.second),
                )
                expected = (
                    StateSort(first, source.side)
                    if node.kind == "anchor"
                    else FunctionSort(
                        StateSort(first, 1 - source.side),
                        StateSort(second, source.side),
                    )
                )
                valid = node.sort == expected
        elif node.kind == "lambda" and type(node.sort) is FunctionSort:
            valid = sorts == (node.sort.codomain,) and (
                0 not in needed or needed[0] == node.sort.domain
            )
            needed = {depth - 1: sort for depth, sort in needed.items() if depth > 0}
        elif (
            node.kind == "apply"
            and len(children) == 2
            and type(sorts[0]) is FunctionSort
        ):
            valid = sorts[1] == sorts[0].domain and node.sort == sorts[0].codomain
        elif node.kind == "call":
            record = self.closure(node.closure, arena, checks)
            if record is not None and record.body.local_id < index:
                valid = node.sort == arena.nodes[
                    record.body.local_id
                ].sort and sorts == tuple(
                    arena.nodes[parameter.local_id].sort for parameter in record.support
                )
        elif node.kind == "finite_apply" and type(node.sort) is StateSort:
            valid = sorts == (node.sort,) and self._finite_function(
                arena, node.sort, node.function
            )
        elif node.kind == "finite_map" and type(node.sort) is StateSort:
            valid = (
                len(sorts) == 1
                and type(sorts[0]) is StateSort
                and self._finite_function(
                    arena, node.sort, node.function, source=sorts[0], normalized=True
                )
            )
        elif (
            node.kind in ("advance", "emit")
            and type(node.action) is ActionProgramID
            and self.action_valid(node.action)
        ) and node.action.owner is arena.actions.token:
            action = arena.actions.node(node.action)
            alphabet = SymbolSort(action.base, action.blank)
            if action.kind == "atom":
                if node.kind == "advance":
                    valid = (
                        node.side in (0, 1)
                        and node.sort == StateSort(node.action, node.side)
                        and sorts == (node.sort, alphabet)
                    )
                else:
                    valid = node.sort == alphabet and sorts == (
                        StateSort(node.action, 0),
                        alphabet,
                        StateSort(node.action, 1),
                    )
        scope = max(needed, default=-1) + 1
        return valid and node.scope == scope, needed

    def closure(
        self,
        value: object,
        arena: BoundaryExpressionArena | None = None,
        checks: list[bool] | None = None,
    ) -> ClosureProgram | None:
        if (
            type(value) is not ClosureProgramID
            or value.kind != "diamond-expression-closure"
            or not _integer(value.local_id)
        ):
            return None
        for root in self.closures:
            if value.owner is root.token and value.local_id < len(root.nodes):
                if arena is not None and root.expressions is not arena:
                    return None
                record = root.nodes[value.local_id]
                if self._closure_record(record, checks):
                    return record
        return None

    def _closure_record(self, record: object, checks: list[bool] | None = None) -> bool:
        root = self.closure_records.get(id(record))
        if root is None or type(record) is not ClosureProgram:
            return False
        arena = root.expressions
        if (
            type(record.parameters) is not tuple
            or not 1 <= len(record.parameters) <= 3
            or type(record.support) is not tuple
        ):
            return False
        for handle in (*record.parameters, record.body, *record.support):
            if (
                type(handle) is not ExprID
                or handle.owner is not arena.token
                or handle.kind != "diamond-boundary-expression"
                or not _integer(handle.local_id)
                or handle.local_id >= len(arena.nodes)
            ):
                return False
            if checks is not None:
                if handle.local_id >= len(checks) or not checks[handle.local_id]:
                    return False
            elif not self.handle(handle, closed=True):
                return False
            if arena.nodes[handle.local_id].scope:
                return False
        if len(set(record.parameters)) != len(record.parameters) or len(
            set(record.support)
        ) != len(record.support):
            return False
        ports = []
        roles = []
        for index, handle in enumerate(record.parameters):
            node = arena.nodes[handle.local_id]
            if node.kind != "port" or type(node.sort) is not StateSort:
                return False
            ports.append(FormalPort(node.sort, node.role))
            roles.append(node.role)
        normalized_roles = tuple(
            f"closure-parameter-{index}" for index in range(len(roles))
        )
        # ``intern`` alpha-normalizes arbitrary callers to the first form.
        # ``intern_canonical`` is restricted to HigherContextArena's stable
        # K/U port contracts so parent construction can reuse a closure
        # without walking and renaming its complete prior expression DAG.
        # Recognize those exact contracts; accepting arbitrary port names here
        # would let caller syntax become semantic identity.
        canonical_roles = (
            ("higher-unary-state",),
            (
                "higher-context-left",
                "higher-context-right",
                "higher-context-incoming",
            ),
        )
        if tuple(roles) != normalized_roles and tuple(roles) not in canonical_roles:
            return False
        body = arena.nodes[record.body.local_id]
        if not set(body.free_ports) <= set(ports):
            return False
        expected = tuple(
            handle
            for handle, port in zip(record.parameters, ports, strict=True)
            if port in body.free_ports
        )
        return record.support == expected

    def _finite_function(
        self,
        arena: BoundaryExpressionArena,
        sort: StateSort | SymbolSort,
        function: object,
        *,
        source: StateSort | None = None,
        normalized: bool = False,
    ) -> bool:
        if (
            type(function) is not TransferSummaryID
            or function.kind != "diamond-finite-expression"
            or function.owner is not arena.boundaries.kernels.owner
            or not self.boundary_valid(function)
        ):
            return False
        if source is None:
            if type(sort) is not StateSort:
                return False
            source = sort
        if not self.sort(source, arena) or not self.sort(sort, arena):
            return False
        key = arena.token, source, sort, function, normalized
        if key in self.finite_checks:
            return self.finite_checks[key]
        kernels = arena.boundaries.kernels
        expression = kernels.expression(function)
        incoming = arena.primitive(source.action)
        if incoming is None:
            return False
        domain = incoming.left_count if source.side == 0 else incoming.right_count
        if type(sort) is StateSort:
            primitive = arena.primitive(sort.action)
            if primitive is None or (primitive.base, primitive.blank) != (
                incoming.base,
                incoming.blank,
            ):
                return False
            codomain = primitive.left_count if sort.side == 0 else primitive.right_count
        else:
            assert isinstance(sort, SymbolSort)
            if (sort.base, sort.blank) != (incoming.base, incoming.blank):
                return False
            codomain = sort.blank + 1
        if expression.domain != codomain or domain <= 0:
            return False
        functions = kernels.functions
        port = LEFT_A if source.side == 0 else RIGHT_A
        width = (domain - 1).bit_length()
        allowed = {
            PortVariable(port.time, port.side, port.role, port.bit + bit)
            for bit in range(width)
        }
        pending = list(expression.bits)
        checked: set[TransferSummaryID] = set()
        while pending:
            bit = pending.pop()
            if (
                type(bit) is not TransferSummaryID
                or not self.boundary_valid(bit)
                or bit.owner is not functions.owner
            ):
                return False
            if bit in checked:
                continue
            checked.add(bit)
            node = functions._nodes[bit.local_id]
            if node.variable is not None:
                if (
                    type(node.variable) is not PortVariable
                    or node.variable not in allowed
                ):
                    return False
                pending.extend(
                    (functions._handle(node.low), functions._handle(node.high))
                )
        for code in range((1 << width) if normalized else domain):
            output = 0
            for bit_number, bit in enumerate(expression.bits):
                index = bit.local_id
                while index >= 2:
                    node = functions._nodes[index]
                    assert node.variable is not None
                    index = (
                        node.high
                        if code & (1 << (width - 1 - node.variable.bit + port.bit))
                        else node.low
                    )
                output |= index << bit_number
            if (code < domain and output >= codomain) or (
                code >= domain and output != 0
            ):
                self.finite_checks[key] = False
                return False
        self.finite_checks[key] = True
        return True

    def _binding(self, value: ExprBinding) -> bool:
        if not self.handle(value.variable, closed=True) or not self.handle(
            value.value, closed=True
        ):
            return False
        first, second = self.expression(value.variable), self.expression(value.value)
        return (
            value.variable.owner is value.value.owner
            and first is not None
            and second is not None
            and first.kind == "port"
            and first.sort == second.sort
        )

    def valid(self, value: object) -> bool:
        if type(value) is LowerFinite:
            return False
        if type(value) is ResolveExpr:
            node = self.expression(value.expression)
            return (
                node is not None
                and bool(node.free_ports)
                and type(node.sort) in (StateSort, FunctionSort)
                and node.kind in ("call", "anchor", "continuation", "apply")
            )
        if type(value) is ClosureProgramID:
            return self.closure(value) is not None
        if type(value) is ClosureProgram:
            return self._closure_record(value)
        if type(value) is ExprID:
            return self.handle(value)
        if type(value) in (StateSort, FunctionSort, SymbolSort):
            return self.sort(value)
        if type(value) is FormalPort:
            return (
                self.sort(value.sort) and type(value.role) is str and bool(value.role)
            )
        if type(value) is BoundaryExprNode:
            return self.records.get(id(value), False)
        if type(value) is ExprBinding:
            return self._binding(value)
        if type(value) is ExprSubstitutionKey:
            if (
                not self.handle(value.expression, closed=True)
                or type(value.bindings) is not tuple
            ):
                return False
            previous = -1
            for binding in value.bindings:
                if type(binding) is not ExprBinding or not self._binding(binding):
                    return False
                if (
                    binding.variable.owner is not value.expression.owner
                    or binding.variable.local_id <= previous
                ):
                    return False
                previous = binding.variable.local_id
            return True
        return False
