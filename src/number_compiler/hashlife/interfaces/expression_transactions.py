"""Expression transactions with one canonical implementation owner."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide, _effect_key
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.execution.diamond_observation_guard import retain_response
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    observation_inputs,
    substitution_bindings,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        BoundaryExpressionArena,
        BoundaryExprNode,
        ExprID,
        ExprSubstitutionKey,
        FormalPort,
        StateSort,
        _Rewrite,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import (
        DiamondKernelArena,
        FiniteExpression,
    )


def _constant_function_value(expression: FiniteExpression) -> int | None:
    """Recover the exact output when every finite-function bit is constant."""
    if not all(bit.local_id < 2 for bit in expression.bits):
        return None
    return sum(
        bit.local_id << bit_number for bit_number, bit in enumerate(expression.bits)
    )


class _Transaction:
    """Local rewrite DAG; no allocation is retained before one reservation."""

    def __init__(self, arena: BoundaryExpressionArena) -> None:
        self.arena = arena
        self.staged: list[BoundaryExprNode] = []
        self.keys: dict[BoundaryExprNode, int] = {}
        self.substitutions: dict[int, int] = {}
        self.substitution_ports: frozenset[FormalPort] = frozenset()
        self.staged_port_references = 0

    def node(self, index: int) -> BoundaryExprNode:
        return self.arena.nodes[index] if index >= 0 else self.staged[-index - 1]

    def _peak(self, name: str, size: int) -> None:
        ledger = self.arena.ledger
        ledger.bump(name, max(0, size - ledger.counters.get(name, 0)))

    def _finite_function_expression(
        self, node: BoundaryExprNode
    ) -> tuple[DiamondKernelArena, TransferSummaryID, FiniteExpression, StateSort]:
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import StateSort

        if node.function is None or type(node.sort) is not StateSort:
            raise ValueError("finite-function node has an invalid owner handle or sort")
        kernels = self.arena.boundaries.kernels
        function_handle = node.function
        return (
            kernels,
            function_handle,
            kernels.expression(function_handle),
            node.sort,
        )

    def intern(self, node: BoundaryExprNode) -> int:
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
            FormalPort,
            _port_order,
        )

        scope = (
            node.bound + 1
            if node.kind == "bound"
            else max((self.node(child).scope for child in node.children), default=0)
        )
        if node.kind == "lambda":
            scope = max(0, scope - 1)
        ports: tuple[FormalPort, ...]
        if node.kind == "port":
            ports = (FormalPort(node.sort, node.role),)
        else:
            ports = tuple(
                sorted(
                    {
                        port
                        for child in node.children
                        for port in self.node(child).free_ports
                    },
                    key=_port_order,
                )
            )
        self.arena.ledger.bump(
            _interfaces_keys.BOUNDARY_EXPRESSION_SUPPORT_CONSTRUCTION_PORTS,
            sum(len(self.node(child).free_ports) for child in node.children),
        )
        self._peak("boundary_expression_support_union_ports_peak", len(ports))
        direct_safe = bool(
            ports
            or scope
            or node.kind in ("literal", "symbol", "port", "bound", "lambda", "pair")
        )
        direct_safe |= (
            node.kind in ("finite_apply", "finite_map")
            and len(node.children) == 1
            and self.node(node.children[0]).kind == "literal"
        )
        children_safe = True
        for child in node.children:
            children_safe &= self.node(child).binding_safe
        self.arena.ledger.bump(
            _interfaces_keys.BOUNDARY_EXPRESSION_BINDING_METADATA_CHILD_READS,
            len(node.children),
        )
        closure_safe = True
        if node.kind == "call":
            if node.closure is None:
                raise ValueError("opaque call has no closure program")
            body = self.arena.closures.resolve(node.closure).body
            closure_safe = self.arena.node(body).binding_safe
            self.arena.ledger.bump(
                _interfaces_keys.BOUNDARY_EXPRESSION_BINDING_METADATA_CLOSURE_READS
            )
        self.arena.ledger.bump(
            _interfaces_keys.BOUNDARY_EXPRESSION_BINDING_METADATA_EVALUATIONS
        )
        node = replace(
            node,
            scope=scope,
            free_ports=ports,
            binding_safe=direct_safe and children_safe and closure_safe,
        )
        if all(child >= 0 for child in node.children):
            found = self.arena.keys.get(node)
            if found is not None:
                self.arena.ledger.bump(_interfaces_keys.BOUNDARY_EXPRESSION_INTERN_HITS)
                return found.local_id
        existing = self.keys.get(node)
        if existing is not None:
            self.arena.ledger.bump(
                _interfaces_keys.BOUNDARY_EXPRESSION_STAGED_INTERNER_HITS
            )
            return existing
        self.staged.append(node)
        result = -len(self.staged)
        self.keys[node] = result
        self._peak("boundary_expression_staged_nodes_peak", len(self.staged))
        self.staged_port_references += len(node.free_ports)
        self._peak(
            "boundary_expression_staged_port_references_peak",
            self.staged_port_references,
        )
        return result

    def _uses_bound(self, root: int) -> bool:
        pending = [(root, 0)]
        seen: set[tuple[int, int]] = set()
        while pending:
            self._peak("boundary_expression_bound_scan_frames_peak", len(pending))
            index, depth = pending.pop()
            self.arena.ledger.bump(
                _interfaces_keys.BOUNDARY_EXPRESSION_BOUND_SCAN_FRAME_POPS
            )
            self._peak("boundary_expression_bound_scan_seen_peak", len(seen))
            self._peak(
                "boundary_expression_bound_scan_workspace_peak",
                len(pending) + len(seen) + 1,
            )
            if (index, depth) in seen:
                continue
            seen.add((index, depth))
            self._peak("boundary_expression_bound_scan_seen_peak", len(seen))
            self.arena.ledger.bump(
                _interfaces_keys.BOUNDARY_EXPRESSION_BOUND_SCAN_VISITS
            )
            node = self.node(index)
            if node.scope <= depth:
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_BOUND_SCAN_EARLY_HITS
                )
                continue
            if node.kind == "bound" and node.bound == depth:
                return True
            pending.extend(
                (child, depth + int(node.kind == "lambda")) for child in node.children
            )
        return False

    def reduce(self, node: BoundaryExprNode) -> int | _Rewrite:
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
            BoundaryExprNode,
            StateSort,
            _Rewrite,
        )

        if node.kind == "call":
            assert node.closure is not None
            record = self.arena.closures.resolve(node.closure)
            if not record.support:
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_CONSTANT_CALL_EARLY_HITS
                )
                return record.body.local_id
            if record.body in record.support:
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_IDENTITY_CALL_EARLY_HITS
                )
                return node.children[record.support.index(record.body)]
            body = self.arena.nodes[record.body.local_id]
            if body.kind in ("anchor", "continuation", "finite_apply", "finite_map"):
                parameter = self.arena._handle(body.children[0])
                if parameter in record.support:
                    argument_index = node.children[record.support.index(parameter)]
                    projected = self.intern(replace(body, children=(argument_index,)))
                    self.arena.ledger.bump(
                        _interfaces_keys.BOUNDARY_EXPRESSION_PROJECTION_CALL_EARLY_HITS
                    )
                    return _Rewrite("normal", projected)
        if node.kind == "finite_map":
            kernels, function_handle, expression, function_sort = (
                self._finite_function_expression(node)
            )
            constant = _constant_function_value(expression)
            if constant is not None:
                return self.intern(
                    BoundaryExprNode("literal", node.sort, value=constant)
                )
            argument = self.node(node.children[0])
            assert type(argument.sort) is StateSort
            primitive = self.arena.primitive(argument.sort.action)
            assert primitive is not None
            domain = len(primitive.domain(BoundarySide(argument.sort.side)))
            port = LEFT_A if argument.sort.side == 0 else RIGHT_A
            if argument.kind == "literal":
                value = kernels.evaluate(
                    function_handle, observation_inputs(domain, port, argument.value)
                )
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_FINITE_FUNCTION_OBSERVATIONS
                )
                return self.intern(BoundaryExprNode("literal", node.sort, value=value))
            if argument.kind in ("finite_apply", "finite_map"):
                assert argument.function is not None
                combined = kernels.substitute(
                    function_handle,
                    substitution_bindings(kernels, domain, port, argument.function),
                )
                from number_compiler.hashlife.interfaces.diamond_finite_map import (
                    admit_map,
                )

                original_sort = self.node(argument.children[0]).sort
                assert type(original_sort) is StateSort
                combined, constant, identity = admit_map(
                    self.arena, original_sort, function_sort, combined
                )
                if identity:
                    return argument.children[0]
                if constant is not None:
                    return self.intern(
                        BoundaryExprNode("literal", node.sort, value=constant)
                    )
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_CROSS_PORT_COMPOSITIONS
                )
                temporary = self.intern(
                    replace(node, function=combined, children=argument.children)
                )
                return _Rewrite("normal", temporary)
        if node.kind == "finite_apply":
            kernels, function_handle, expression, function_sort = (
                self._finite_function_expression(node)
            )
            constant = _constant_function_value(expression)
            if constant is not None:
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_CONSTANT_FUNCTION_EARLY_HITS
                )
                return self.intern(
                    BoundaryExprNode("literal", node.sort, value=constant)
                )
            argument = self.node(node.children[0])
            port = LEFT_A if function_sort.side == 0 else RIGHT_A
            if argument.kind == "literal":
                value = kernels.evaluate(
                    function_handle,
                    observation_inputs(expression.domain, port, argument.value),
                )
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_FINITE_FUNCTION_OBSERVATIONS
                )
                return self.intern(BoundaryExprNode("literal", node.sort, value=value))
            if argument.kind == "finite_apply" and argument.sort == node.sort:
                assert argument.function is not None
                primitive_handle = kernels._kernel_ids[
                    _effect_key(self.arena.actions.primitive(function_sort.action))
                ]
                combined = self.arena.unary.compose(
                    primitive_handle,
                    function_sort.side,
                    argument.function,
                    function_handle,
                    port,
                )
                # Schedule a normal reduction of this new composition, so a
                # constant result can drop the remaining argument immediately.
                combined_node = replace(
                    node, function=combined, children=argument.children
                )
                temporary = self.intern(combined_node)
                return _Rewrite("normal", temporary)
        if node.kind in ("advance", "emit"):
            arguments = tuple(self.node(child) for child in node.children)
            kinds = tuple(argument.kind for argument in arguments)
            expected = (
                ("literal", "symbol")
                if node.kind == "advance"
                else ("literal", "symbol", "literal")
            )
            if kinds == expected:
                assert node.action is not None
                primitive = self.arena.primitive(node.action)
                if primitive is not None:
                    values = tuple(argument.value for argument in arguments)
                    self.arena.ledger.bump(
                        _interfaces_keys.BOUNDARY_EXPRESSION_CONSTANT_KERNEL_REDUCTIONS
                    )
                    if node.kind == "advance":
                        result = primitive.advance(
                            BoundarySide(node.side), values[0], values[1]
                        )
                        return self.intern(
                            BoundaryExprNode("literal", node.sort, value=result)
                        )
                    result = primitive.emit(values[0], values[1], values[2])
                    return self.intern(
                        BoundaryExprNode("symbol", node.sort, value=result)
                    )
        if node.kind in ("anchor", "continuation"):
            child = self.node(node.children[0])
            if child.kind == "pair":
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_PROJECTION_REDUCTIONS
                )
                return child.children[int(node.kind == "continuation")]
        elif node.kind == "pair":
            anchor, continuation = (self.node(child) for child in node.children)
            if (
                anchor.kind == "anchor"
                and continuation.kind == "continuation"
                and anchor.children == continuation.children
            ):
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_ETA_REDUCTIONS
                )
                return anchor.children[0]
        elif node.kind == "apply":
            function = self.node(node.children[0])
            if function.kind == "lambda":
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_BETA_REDUCTIONS
                )
                return _Rewrite(
                    "beta", function.children[0], parameter=node.children[1]
                )
        elif node.kind == "lambda":
            body = self.node(node.children[0])
            if body.kind == "apply":
                argument = self.node(body.children[1])
                if (
                    argument.kind == "bound"
                    and argument.bound == 0
                    and not self._uses_bound(body.children[0])
                ):
                    self.arena.ledger.bump(
                        _interfaces_keys.BOUNDARY_EXPRESSION_ETA_REDUCTIONS
                    )
                    return _Rewrite("shift", body.children[0], parameter=-1)
        return self.intern(node)

    def rewrite(self, initial: _Rewrite) -> int:
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
            BoundaryExprNode,
            FormalPort,
            _Rewrite,
        )

        results: dict[_Rewrite, int] = {}
        dependencies: dict[_Rewrite, tuple[_Rewrite, ...]] = {}
        dependency_slots = 0
        pending = [(initial, 0)]
        while pending:
            self._peak("boundary_expression_rewrite_frames_peak", len(pending))
            self._peak("boundary_expression_rewrite_results_peak", len(results))
            self._peak(
                "boundary_expression_rewrite_dependencies_peak", len(dependencies)
            )
            self._peak(
                "boundary_expression_rewrite_dependency_slots_peak", dependency_slots
            )
            task, phase = pending.pop()
            self.arena.ledger.bump(_interfaces_keys.BOUNDARY_EXPRESSION_REWRITE_VISITS)
            if task in results:
                continue
            node = self.node(task.root)
            if phase == 2:
                dependency = dependencies.pop(task)
                dependency_slots -= len(dependency)
                results[task] = results[dependency[0]]
                continue
            if phase == 0 and task.mode == "normal":
                reduced_root = self.reduce(node)
                if isinstance(reduced_root, int):
                    results[task] = reduced_root
                else:
                    dependencies[task] = (reduced_root,)
                    dependency_slots += 1
                    pending.extend(((task, 2), (reduced_root, 0)))
                continue
            if phase == 0:
                proof = ""
                if task.mode == "shift" and task.parameter == 0:
                    proof = "zero_shift"
                elif task.mode in ("shift", "beta") and node.scope <= task.depth:
                    proof = "bound_scope"
                elif task.mode == "free" and self.substitution_ports.isdisjoint(
                    node.free_ports
                ):
                    proof = "unaffected_free_ports"
                elif task.mode == "abstract":
                    target = self.node(task.parameter)
                    if FormalPort(target.sort, target.role) not in node.free_ports:
                        proof = "absent_binder"
                if proof:
                    self.arena.ledger.bump(
                        _interfaces_keys.BOUNDARY_EXPRESSION_REWRITE_EARLY_HITS
                    )
                    self.arena.ledger.bump(
                        "boundary_expression_" + proof + "_early_hits"
                    )
                    results[task] = task.root
                    continue
                replacement: int | _Rewrite | None = None
                if task.mode == "free" and task.root in self.substitutions:
                    replacement = self.substitutions[task.root]
                elif task.mode == "abstract" and task.root == task.parameter:
                    replacement = self.intern(
                        BoundaryExprNode("bound", node.sort, bound=task.depth)
                    )
                elif node.kind == "bound":
                    if task.mode == "beta" and node.bound == task.depth:
                        replacement = _Rewrite(
                            "shift", task.parameter, parameter=task.depth
                        )
                    elif task.mode == "beta" and node.bound > task.depth:
                        replacement = self.intern(replace(node, bound=node.bound - 1))
                    elif task.mode == "shift" and node.bound >= task.depth:
                        replacement = self.intern(
                            replace(node, bound=node.bound + task.parameter)
                        )
                if isinstance(replacement, int):
                    results[task] = replacement
                    continue
                if replacement is not None:
                    dependencies[task] = (replacement,)
                    dependency_slots += 1
                    pending.extend(((task, 2), (replacement, 0)))
                    continue
                depth = (
                    0
                    if task.mode == "free"
                    else task.depth + int(node.kind == "lambda")
                )
                children = tuple(
                    _Rewrite(task.mode, child, depth, task.parameter)
                    for child in node.children
                )
                dependencies[task] = children
                dependency_slots += len(children)
                pending.append((task, 1))
                pending.extend((child, 0) for child in reversed(children))
                continue
            dependency = dependencies.pop(task)
            dependency_slots -= len(dependency)
            rewritten_children = tuple(results[child] for child in dependency)
            if task.mode != "normal" and rewritten_children == node.children:
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_UNCHANGED_CHILDREN_LATE_HITS
                )
                results[task] = task.root
                continue
            reduced = self.reduce(replace(node, children=rewritten_children))
            if isinstance(reduced, int):
                results[task] = reduced
            else:
                dependencies[task] = (reduced,)
                dependency_slots += 1
                pending.extend(((task, 2), (reduced, 0)))
        self._peak("boundary_expression_rewrite_results_peak", len(results))
        return results[initial]

    def publish(self, root: int, memo: ExprSubstitutionKey | None = None) -> ExprID:
        if self.node(root).scope:
            raise ValueError("expression has an unbound de Bruijn variable")
        if memo is not None:
            keep, visits, peak = retain_response(
                self.node,
                root,
                tuple(binding.value.local_id for binding in memo.bindings),
            )
            self.arena.ledger.bump(_shared_keys.BOUND_RESPONSE_GUARD_VISITS, visits)
            self._peak("bound_response_guard_workspace_peak", peak)
            if not keep:
                memo = None
                self.arena.ledger.bump(
                    _interfaces_keys.BOUNDARY_EXPRESSION_BOUND_RESULT_MEMO_DROPS
                )
        reachable: set[int] = set()
        pending = [root]
        while pending:
            self._peak("boundary_expression_publication_frames_peak", len(pending))
            index = pending.pop()
            if index >= 0 or index in reachable:
                continue
            reachable.add(index)
            self._peak("boundary_expression_publication_seen_peak", len(reachable))
            pending.extend(self.node(index).children)
        count = len(reachable)
        self.arena.ledger.reserve_many(
            (
                (self.arena.node_owner, count, count),
                (self.arena.key_owner, count, 0),
                (self.arena.memo_owner, int(memo is not None), 0),
            )
        )
        published: dict[int, int] = {}
        for offset, node in enumerate(self.staged):
            local = -offset - 1
            if local not in reachable:
                continue
            children = tuple(
                child if child >= 0 else published[child] for child in node.children
            )
            actual = replace(node, children=children)
            index = len(self.arena.nodes)
            self.arena.nodes.append(actual)
            self.arena.keys[actual] = self.arena._handle(index)
            published[local] = index
            self._peak("boundary_expression_publication_map_peak", len(published))
            self.arena.ledger.bump(
                _interfaces_keys.BOUNDARY_EXPRESSION_RETAINED_FREE_PORT_REFERENCES,
                len(actual.free_ports),
            )
            self._peak("boundary_expression_max_free_ports", len(actual.free_ports))
        result = self.arena._handle(root if root >= 0 else published[root])
        if memo is not None:
            self.arena.memo[memo] = result
        self.arena.ledger.bump(
            _interfaces_keys.BOUNDARY_EXPRESSION_PUBLISHED_NODES, count
        )
        self.arena.ledger.bump(
            _interfaces_keys.BOUNDARY_EXPRESSION_DISCARDED_NODES,
            len(self.staged) - count,
        )
        return result
