"""Prevent bound program responses from becoming an implicit future-value tape.

Canonical literals and complete primitive-function inputs remain reusable.
This guard concerns response bindings; it never removes semantic program nodes.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        BoundaryExpressionArena,
        BoundaryExprNode,
        ExprID,
    )


def realized_result(
    node_at: Callable[[int], BoundaryExprNode], root: int
) -> tuple[bool, int, int]:
    pending = [root]
    seen: set[int] = set()
    visits = peak = 0
    while pending:
        peak = max(peak, len(pending) + len(seen))
        index = pending.pop()
        visits += 1
        if index in seen:
            continue
        seen.add(index)
        node = node_at(index)
        if node.kind not in ("literal", "symbol", "pair", "lambda", "bound"):
            return False, visits, max(peak, len(seen))
        pending.extend(node.children)
    return True, visits, max(peak, len(seen))


def _bound_input(
    node_at: Callable[[int], BoundaryExprNode], root: int
) -> tuple[bool, int]:
    node = node_at(root)
    if node.free_ports or node.kind in ("literal", "symbol"):
        return False, 1
    # A complete finite map plus a canonical incoming finite value is a
    # semantic interface key, unlike an arbitrary closed expression program.
    if (
        node.kind in ("finite_apply", "finite_map")
        and node.function is not None
        and len(node.children) == 1
    ):
        return node_at(node.children[0]).kind != "literal", 2
    return True, 1


def bound_program_input(node_at: Callable[[int], BoundaryExprNode], root: int) -> bool:
    return _bound_input(node_at, root)[0]


def retain_response(
    node_at: Callable[[int], BoundaryExprNode], result: int, inputs: Sequence[int]
) -> tuple[bool, int, int]:
    # A reduced complete function can encode a captured provider symbol even
    # when its formal input remains free. Erasing captured-program provenance
    # must not publish an occurrence-to-finite-effect response binding.
    unsafe = False
    for argument in inputs:
        unsafe |= not node_at(argument).binding_safe
    result_node = node_at(result)
    metadata_reads = len(inputs) + 1
    if unsafe and result_node.binding_safe:
        return False, metadata_reads, len(inputs)
    bound = False
    input_visits = metadata_reads
    for argument in inputs:
        forbidden, visits = _bound_input(node_at, argument)
        bound |= forbidden
        input_visits += visits
    if not bound:
        return True, input_visits, len(inputs)
    realized, visits, peak = realized_result(node_at, result)
    return not realized, visits + input_visits, max(peak, len(inputs))


def retain_expression_response(
    arena: BoundaryExpressionArena, result: ExprID, inputs: Sequence[ExprID]
) -> bool:
    root = arena._resolve(result)
    arguments = tuple(arena._resolve(argument) for argument in inputs)
    keep, visits, peak = retain_response(arena.nodes.__getitem__, root, arguments)
    arena.ledger.bump("bound_response_guard_visits", visits)
    name = "bound_response_guard_workspace_peak"
    arena.ledger.bump(name, max(0, peak - arena.ledger.counters.get(name, 0)))
    return keep
