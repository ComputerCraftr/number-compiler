"""Canonical primitive-pair transfer through finite-function substitution.

For a composed boundary (a,F), one symbol updates the complete continuation as
F'(r) = delta_B(F(delta_A_opposite(r,s)), emit_A(a,s,r)). The mirrored case swaps
the emit ports. Boolean function composition performs this update before any
parent boundary ID is published; no per-argument scheduler execution is needed.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryStateID,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    from_expression,
    input_variable,
    to_expression,
)
from number_compiler.hashlife.interfaces.diamond_unary import PrimitiveUnaryFunctions
from number_compiler.resources.ledger import OwnedMemo


@dataclass(frozen=True, slots=True)
class PrimitivePairKey:
    action: ActionProgramID
    state: BoundaryStateID
    side: int
    symbol: int


class PrimitivePairActions:
    """Finite local interface cache, never a coordinate-indexed emitted field."""

    def __init__(
        self,
        boundaries: BoundaryActionArena,
        unary: PrimitiveUnaryFunctions | None = None,
    ) -> None:
        self.boundaries = boundaries
        self.actions, self.kernels, self.ledger = (
            boundaries.temporals,
            boundaries.kernels,
            boundaries.ledger,
        )
        if unary is not None and unary.kernels is not self.kernels:
            raise ValueError("primitive pair functions belong to another kernel arena")
        self.unary = PrimitiveUnaryFunctions(self.kernels) if unary is None else unary
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"diamond-primitive-pairs-{len(self.ledger.inventory())}", "query_memo"
        )
        self._transitions: OwnedMemo[PrimitivePairKey, BoundaryStateID] = OwnedMemo(
            self.ledger, owner, evictable=True
        )

    def supports(self, action: ActionProgramID) -> bool:
        node = self.actions.resolve(action)
        return node.kind == "compose" and all(
            self.actions.node(self.actions.reference(child)).kind == "atom"
            for child in (node.first, node.second)
        )

    def advance(
        self, action: ActionProgramID, state: BoundaryStateID, side: int, symbol: int
    ) -> BoundaryStateID:
        node, boundary = self.actions.resolve(action), self.boundaries.state(state)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("invalid primitive-pair direction")
        if not self.supports(action) or (boundary.action, boundary.side) != (
            action,
            side,
        ):
            raise ValueError(
                "primitive-pair transition has the wrong boundary interface"
            )
        if type(symbol) is not int or not 0 <= symbol <= node.blank:
            raise ValueError("symbol outside the primitive-pair alphabet")
        if boundary.anchor is None or boundary.continuation is None:
            raise ValueError("primitive-pair state requires an anchor and continuation")
        key = PrimitivePairKey(action, state, side, symbol)
        self.ledger.bump("diamond_primitive_pair_requests")
        cached = self._transitions.get(key)
        if cached is not None:
            self.ledger.bump("diamond_primitive_pair_hits")
            return cached
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        first_id = self.kernels.intern(self.actions.primitive(first))
        second_id = self.kernels.intern(self.actions.primitive(second))
        primitive = self.kernels.kernel(first_id)
        anchor = self.boundaries.state(boundary.anchor)
        function = self.boundaries.action(boundary.continuation)
        signature = function.signature
        if anchor.literal < 0 or signature is None or signature.input_size is None:
            raise ValueError(
                "primitive pair requires finite anchor and function domains"
            )
        port, variable = input_variable(self.boundaries, first, 1 - side)
        argument_map = self.kernels.advance_expression(
            first_id,
            BoundarySide(1 - side),
            variable,
            self.kernels.constant(primitive.blank + 1, symbol),
        )
        previous = to_expression(self.boundaries, boundary.continuation, port)
        previous = self.unary.compose(first_id, 1 - side, argument_map, previous, port)
        anchor_value = self.kernels.constant(
            len(primitive.domain(BoundarySide(side))), anchor.literal
        )
        left, right = (
            (anchor_value, variable) if side == 0 else (variable, anchor_value)
        )
        emitted = self.kernels.emit_expression(
            first_id,
            left,
            self.kernels.constant(primitive.blank + 1, symbol),
            right,
        )
        following = self.unary.mapped(
            first_id, 1 - side, port, second_id, "advance", side, (previous, emitted)
        )
        continuation = from_expression(self.boundaries, following, signature, port)
        next_anchor = self.boundaries.literal(
            first,
            side,
            primitive.advance(BoundarySide(side), anchor.literal, symbol),
        )
        result = self.boundaries.pair(action, side, next_anchor, continuation)
        self._transitions[key] = result
        self.ledger.bump("diamond_primitive_pair_evaluations")
        return result
