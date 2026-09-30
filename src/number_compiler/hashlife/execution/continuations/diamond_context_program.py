"""Lazy finite-port programs for the spatial half of a temporal diamond.

Spatial composition retains function composition, not its full three-port truth
table. Observation substitutes the demanded ports before primitive reduction.
These are syntax-canonical program IDs; boundary results have finite-function
canonical IDs. No context program contains an emitted word or cell provenance.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryActionArena
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    scan_primitive_support,
    substitution_bindings,
)
from number_compiler.hashlife.interfaces.diamond_unary import PrimitiveUnaryFunctions
from number_compiler.resources.ledger import OwnedMemo

LEFT_A = PortVariable(0, 0, "diamond-pair-left-a", 0)
RIGHT_A = PortVariable(0, 1, "diamond-pair-right-a", 0)


@dataclass(frozen=True, slots=True)
class ContextProgramID(ArenaHandle):
    """A complete finite-port composition, without a bound observation."""


@dataclass(frozen=True, slots=True)
class ContextNode:
    kind: Literal["leaf", "join"]
    action: ActionProgramID
    symbol: int = -1
    left: ContextProgramID | None = None
    right: ContextProgramID | None = None
    middle_left: TransferSummaryID | None = None
    middle_right: TransferSummaryID | None = None


@dataclass(frozen=True, slots=True)
class ContextObservation:
    program: ContextProgramID
    left: TransferSummaryID
    right: TransferSummaryID
    incoming: TransferSummaryID
    side: int


class ContextProgramArena:
    def __init__(self, boundaries: BoundaryActionArena) -> None:
        self.boundaries, self.kernels = boundaries, boundaries.kernels
        self.actions, self.ledger = boundaries.temporals, boundaries.ledger
        self.unary = PrimitiveUnaryFunctions(self.kernels)
        self.token = ArenaToken("diamond-context-programs")
        self.ledger.register_execution_root(self)
        prefix = f"diamond-context-{len(self.ledger.inventory())}"
        self.node_owner = self.ledger.register(prefix + "-nodes", "context_program")
        self.id_owner = self.ledger.register(
            prefix + "-ids", "context_program_interner"
        )
        self._nodes: MutableSequence[ContextNode] = self.ledger.make_list(
            self.node_owner
        )
        self._ids: MutableMapping[ContextNode, ContextProgramID] = (
            self.ledger.make_dict(self.id_owner)
        )
        self.observations: OwnedMemo[ContextObservation, TransferSummaryID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-observations", "query_memo"),
            evictable=True,
        )
        self.kernel_ids: OwnedMemo[
            ActionProgramID, tuple[ActionProgramID, ActionProgramID]
        ] = OwnedMemo(
            self.ledger,
            self.ledger.register(
                prefix + "-kernel-interfaces", "finite_kernel_interface"
            ),
        )

    def resolve(self, handle: ContextProgramID) -> ContextNode:
        if type(handle) is not ContextProgramID:
            raise TypeError("expected a finite context program")
        handle.validate(self.token, "diamond-context-program", size=len(self._nodes))
        return self._nodes[handle.local_id]

    def interfaces(
        self, action: ActionProgramID
    ) -> tuple[ActionProgramID, ActionProgramID]:
        node = self.actions.resolve(action)
        if node.kind != "compose":
            raise ValueError("context program requires two primitive interfaces")
        children = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        if any(self.actions.node(child).kind != "atom" for child in children):
            raise ValueError("context program requires two primitive interfaces")
        return children

    def _intern(self, node: ContextNode) -> ContextProgramID:
        found = self._ids.get(node)
        if found is not None:
            self.ledger.bump("context_program_interner_requests")
            self.ledger.bump("context_program_interner_hits")
            return found
        self.ledger.reserve_many(((self.node_owner, 1, 1), (self.id_owner, 1, 0)))
        handle = ContextProgramID(
            self.token, "diamond-context-program", len(self._nodes)
        )
        self._nodes.append(node)
        self._ids[node] = handle
        self.ledger.bump("context_program_interner_requests")
        self.ledger.bump("context_program_interner_evaluations")
        return handle

    def leaf(self, action: ActionProgramID, symbol: int) -> ContextProgramID:
        first, second = self.interfaces(action)
        if (
            type(symbol) is not int
            or not 0 <= symbol <= self.actions.node(action).blank
        ):
            raise ValueError(
                "context leaf requires an original kernel-alphabet parameter"
            )
        if action not in self.kernel_ids:
            self.kernel_ids[action] = (
                self.kernels.intern(self.actions.primitive(first)),
                self.kernels.intern(self.actions.primitive(second)),
            )
        return self._intern(ContextNode("leaf", action, symbol))

    def join(
        self,
        action: ActionProgramID,
        left: ContextProgramID,
        right: ContextProgramID,
        middle_left: TransferSummaryID,
        middle_right: TransferSummaryID,
    ) -> ContextProgramID:
        self.interfaces(action)
        low, high = self.resolve(left), self.resolve(right)
        if low.action != action or high.action != action:
            raise ValueError("spatial context interfaces disagree")
        a = self.kernels.kernel(self.kernel_ids[action][0])
        if (
            self.kernels.expression(middle_left).domain,
            self.kernels.expression(middle_right).domain,
        ) != (
            a.left_count,
            a.right_count,
        ):
            raise ValueError("spatial midpoint domains disagree")
        return self._intern(
            ContextNode(
                "join",
                action,
                left=left,
                right=right,
                middle_left=middle_left,
                middle_right=middle_right,
            )
        )

    def _validate(
        self, request: ContextObservation
    ) -> tuple[ActionProgramID, ActionProgramID]:
        node = self.resolve(request.program)
        self.interfaces(node.action)
        if type(request.side) is not int or request.side not in (0, 1):
            raise ValueError("invalid context direction")
        # Validate all handles before kernel admission can mutate an arena.
        expressions = tuple(
            self.kernels.expression(value)
            for value in (request.left, request.right, request.incoming)
        )
        aid, bid = self.kernel_ids[node.action]
        ak, bk = self.kernels.kernel(aid), self.kernels.kernel(bid)
        if tuple(value.domain for value in expressions) != (
            ak.left_count,
            ak.right_count,
            bk.left_count if request.side == 0 else bk.right_count,
        ):
            raise ValueError("context observation has incompatible finite ports")
        return aid, bid

    def _substitute(
        self, function: TransferSummaryID, port: PortVariable, value: TransferSummaryID
    ) -> TransferSummaryID:
        return self.kernels.substitute(
            function,
            substitution_bindings(
                self.kernels, self.kernels.expression(value).domain, port, value
            ),
        )

    def _input_port(
        self, arguments: tuple[TransferSummaryID, ...]
    ) -> tuple[int, PortVariable] | None:
        pending = [
            bit
            for argument in arguments
            for bit in self.kernels.expression(argument).bits
        ]
        ports = scan_primitive_support(
            self.kernels, pending, None, "context_variable_support", ""
        )
        if ports == {(0, 0, LEFT_A.role)}:
            return 0, LEFT_A
        if ports == {(0, 1, RIGHT_A.role)}:
            return 1, RIGHT_A
        return None

    def execute(
        self,
        program: ContextProgramID,
        left: TransferSummaryID,
        right: TransferSummaryID,
        incoming: TransferSummaryID,
        side: int,
    ) -> TransferSummaryID:
        root = ContextObservation(program, left, right, incoming, side)
        self._validate(root)
        # Each frame is one dependency on a canonical function program. Stacks
        # follow spatial joins and never contain temporal-stage carry arrays.
        pending: list[tuple[ContextObservation, int, ContextObservation | None]] = [
            (root, 0, None)
        ]
        while pending:
            peak = self.ledger.counters.get("context_program_workspace_peak", 0)
            self.ledger.bump(
                "context_program_workspace_peak", max(0, len(pending) - peak)
            )
            request, phase, previous = pending.pop()
            aid, bid = self._validate(request)
            if phase == 0:
                self.ledger.bump("context_observation_requests")
                if request in self.observations:
                    self.ledger.bump("context_observation_cache_hits")
                    continue
            node = self.resolve(request.program)
            if node.kind == "leaf":
                symbol = self.kernels.constant(
                    self.kernels.kernel(aid).blank + 1, node.symbol
                )
                port = self._input_port((request.left, request.right, request.incoming))
                if port is None:
                    emitted = self.kernels.emit_expression(
                        aid, request.left, symbol, request.right
                    )
                    result = self.kernels.advance_expression(
                        bid, BoundarySide(request.side), request.incoming, emitted
                    )
                else:
                    input_side, variable = port
                    emitted = self.unary.mapped(
                        aid,
                        input_side,
                        variable,
                        aid,
                        "emit",
                        0,
                        (request.left, symbol, request.right),
                    )
                    result = self.unary.mapped(
                        aid,
                        input_side,
                        variable,
                        bid,
                        "advance",
                        request.side,
                        (request.incoming, emitted),
                    )
            else:
                assert node.left is not None and node.right is not None
                assert node.middle_left is not None and node.middle_right is not None
                middle_left = self._substitute(node.middle_left, LEFT_A, request.left)
                middle_right = self._substitute(
                    node.middle_right, RIGHT_A, request.right
                )
                if phase == 0:
                    child = (
                        ContextObservation(
                            node.left, request.left, middle_right, request.incoming, 0
                        )
                        if request.side == 0
                        else ContextObservation(
                            node.right, middle_left, request.right, request.incoming, 1
                        )
                    )
                    pending.extend(((request, 1, child), (child, 0, None)))
                    continue
                assert previous is not None
                if phase == 1:
                    child = (
                        ContextObservation(
                            node.right,
                            middle_left,
                            request.right,
                            self.observations[previous],
                            0,
                        )
                        if request.side == 0
                        else ContextObservation(
                            node.left,
                            request.left,
                            middle_right,
                            self.observations[previous],
                            1,
                        )
                    )
                    pending.extend(((request, 2, child), (child, 0, None)))
                    continue
                result = self.observations[previous]
            self.observations[request] = result
            self.ledger.bump("context_observation_evaluations")
        return self.observations[root]
