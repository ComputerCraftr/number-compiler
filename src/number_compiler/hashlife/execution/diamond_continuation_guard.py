"""Admission of generic finite-function memo bindings without captured outputs.

A syntactically free port is insufficient: a complete function can encode a
future symbol in its constants even when its argument matters. Generic compiler
memoization therefore accepts only universally open kernel programs. Source-cell
transfer bindings have a separate typed parent interface and are not judged by
this predicate.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        BoundaryExpressionArena,
        ExprID,
    )


def function_program_admission(
    arena: BoundaryExpressionArena, expression: ExprID
) -> tuple[bool, int, int]:
    """Validate scope, then read the independently derived immutable proof bit.

    The expression interner derives this flag from each constructor's closure
    status, child flags, and opaque closure body flag. This query does not walk
    source children or repeat the proof on a warm canonical program.
    """
    return arena.node(expression).binding_safe, 1, 1
