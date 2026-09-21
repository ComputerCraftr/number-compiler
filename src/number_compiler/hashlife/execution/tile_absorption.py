"""Store-free structured boundary algebra for tile absorption.

The tile scheduler owns occurrence/result memoization.  This module only
constructs canonical functions in the runtime's existing semantic arenas. In
particular it owns no provider chain, cache, source binding, or runtime-value
evaluator.

For adjacent spatial cells ``L`` and ``R``, a left boundary crosses ``L``
then ``R`` while a right boundary crosses ``R`` then ``L``.  Representing the
two transfers as canonical curried functions makes that directional law a
small semantic operation which can be reused at every spatial level.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)


@dataclass(frozen=True, slots=True)
class StructuredBoundaryTransfer:
    """Canonical two-sided transfer and its typed product representation."""

    left: StructureID
    right: StructureID
    product: StructureID


@dataclass(frozen=True, slots=True)
class HigherBoundaryTransfer:
    """Two directional transfers over an arbitrary composed action state sort.

    Inputs remain two named higher state variables.  A composed state may
    itself contain a function; it is substituted as one canonical expression
    and never converted to a finite integer port or enumerated domain.
    """

    action: FieldCellActionID
    left_input: HigherExpressionID
    right_input: HigherExpressionID
    left: HigherExpressionID
    right: HigherExpressionID


@dataclass(frozen=True, slots=True)
class HigherSpatialWiring:
    """Canonical midpoint wiring and composed two-sided transfer."""

    transfer: HigherBoundaryTransfer
    left_mid: HigherExpressionID
    right_mid: HigherExpressionID


def _validate_higher_transfer(
    semantics: HigherSemanticArena,
    transfer: HigherBoundaryTransfer,
) -> None:
    if type(transfer) is not HigherBoundaryTransfer:
        raise TypeError("higher boundary composition requires a typed transfer")
    semantics.schema.validate_action(transfer.action)
    expected_left = semantics.state_sort(transfer.action, 0)
    expected_right = semantics.state_sort(transfer.action, 1)
    for reference, expected, role in (
        (transfer.left_input, expected_left, "left input"),
        (transfer.right_input, expected_right, "right input"),
        (transfer.left, expected_left, "left result"),
        (transfer.right, expected_right, "right result"),
    ):
        node = semantics.expression(reference)
        if node.sort != expected:
            raise ValueError(f"higher boundary {role} has another action state sort")
    if (
        semantics.expression(transfer.left_input).kind != "variable"
        or semantics.expression(transfer.right_input).kind != "variable"
    ):
        raise ValueError("higher boundary inputs must be canonical state variables")


def higher_boundary_transfer(
    semantics: HigherSemanticArena,
    action: FieldCellActionID,
    left_input: HigherExpressionID,
    right_input: HigherExpressionID,
    left: HigherExpressionID,
    right: HigherExpressionID,
) -> HigherBoundaryTransfer:
    """Validate one source-free transfer over possibly functional states."""
    result = HigherBoundaryTransfer(action, left_input, right_input, left, right)
    _validate_higher_transfer(semantics, result)
    return result


def _bind_higher(
    semantics: HigherSemanticArena,
    transfer: HigherBoundaryTransfer,
    expression: HigherExpressionID,
    left: HigherExpressionID,
    right: HigherExpressionID,
) -> HigherExpressionID:
    return semantics.bind_free_many(
        expression, ((transfer.left_input, left), (transfer.right_input, right))
    )


def compose_higher_spatial_transfers(
    semantics: HigherSemanticArena,
    first: HigherBoundaryTransfer,
    second: HigherBoundaryTransfer,
) -> HigherBoundaryTransfer:
    """Compose adjacent cells over recursive product/function state sorts.

    This is the higher-state form of the two midpoint equations copied from
    ``HigherSpatialMacroComposer._combine``.  It constructs semantic DAG nodes
    only; it never asks the runtime-value evaluator to apply a continuation.
    """
    return compose_higher_spatial_wiring(semantics, first, second).transfer


def compose_higher_spatial_wiring(
    semantics: HigherSemanticArena,
    first: HigherBoundaryTransfer,
    second: HigherBoundaryTransfer,
) -> HigherSpatialWiring:
    """Compose adjacent transfers and retain their two midpoint expressions.

    The midpoint expressions are needed to bind the children's output and
    summary components.  Keeping their construction here prevents the live
    macro composer from maintaining a second copy of the directional laws.
    """
    if type(semantics) is not HigherSemanticArena:
        raise TypeError("higher spatial composition requires higher semantics")
    _validate_higher_transfer(semantics, first)
    _validate_higher_transfer(semantics, second)
    if (
        first.action != second.action
        or first.left_input != second.left_input
        or first.right_input != second.right_input
    ):
        raise ValueError(
            "higher spatial children require one action and port declaration"
        )
    incoming_left, incoming_right = first.left_input, first.right_input
    left_mid = _bind_higher(
        semantics,
        first,
        first.left,
        incoming_left,
        incoming_right,
    )
    right_mid = _bind_higher(
        semantics,
        second,
        second.right,
        incoming_left,
        incoming_right,
    )
    boundary_left = _bind_higher(
        semantics,
        second,
        second.left,
        left_mid,
        incoming_right,
    )
    boundary_right = _bind_higher(
        semantics,
        first,
        first.right,
        incoming_left,
        right_mid,
    )
    return HigherSpatialWiring(
        higher_boundary_transfer(
            semantics,
            first.action,
            incoming_left,
            incoming_right,
            boundary_left,
            boundary_right,
        ),
        left_mid,
        right_mid,
    )


def _endomorphism_sort(port: FinitePort) -> FunctionSort:
    return FunctionSort((port,), AtomSort(port.variable.role, port.cardinality))


def _validate_endomorphism(
    structures: StructureArena,
    value: StructureID,
    port: FinitePort,
) -> None:
    node = structures.resolve(value)
    expected = FunctionSignature((), _endomorphism_sort(port))
    if node.kind != "function" or node.signature != expected:
        raise ValueError("boundary transfer has another canonical function sort")


def boundary_endomorphism(
    structures: StructureArena,
    port: FinitePort,
    body: FactoredFunctionID,
) -> StructureID:
    """Curry one total finite state transition into a canonical function."""
    if type(structures) is not StructureArena or type(port) is not FinitePort:
        raise TypeError("boundary endomorphism requires structured finite semantics")
    function = structures.bits.resolve(body)
    expected = FunctionSignature(
        (port,), AtomSort(port.variable.role, port.cardinality)
    )
    if function.signature != expected:
        raise ValueError("boundary transition has another finite state domain")
    return structures.curry(structures.atom(body), (port,))


def compose_endomorphisms(
    structures: StructureArena,
    before: StructureID,
    after: StructureID,
    port: FinitePort,
) -> StructureID:
    """Return ``after(before(state))`` without enumerating the state domain."""
    if type(structures) is not StructureArena or type(port) is not FinitePort:
        raise TypeError("boundary composition requires structured finite semantics")
    _validate_endomorphism(structures, before, port)
    _validate_endomorphism(structures, after, port)
    state_sort = AtomSort(port.variable.role, port.cardinality)
    variable = structures.bits.variable((port,), port, state_sort)
    first = structures.apply(before, {port.variable: variable})
    first_node = structures.resolve(first)
    if first_node.kind != "atom" or first_node.atom is None:
        raise ValueError("boundary transfer did not return one finite state")
    second = structures.apply(after, {port.variable: first_node.atom})
    return structures.curry(second, (port,))


def boundary_transfer(
    structures: StructureArena,
    left: StructureID,
    right: StructureID,
    left_port: FinitePort,
    right_port: FinitePort,
) -> StructuredBoundaryTransfer:
    """Validate and bundle one complete directed boundary-transfer pair."""
    _validate_endomorphism(structures, left, left_port)
    _validate_endomorphism(structures, right, right_port)
    return StructuredBoundaryTransfer(left, right, structures.product((left, right)))


def compose_spatial_transfers(
    structures: StructureArena,
    first: StructuredBoundaryTransfer,
    second: StructuredBoundaryTransfer,
    left_port: FinitePort,
    right_port: FinitePort,
) -> StructuredBoundaryTransfer:
    """Compose adjacent spatial cells using both causal directions.

    ``first`` is the left child and ``second`` is the right child.  The order
    reversal for the right transfer is the two-sided midpoint equation used by
    the tile HashLife scheduler.
    """
    if (
        type(first) is not StructuredBoundaryTransfer
        or type(second) is not StructuredBoundaryTransfer
    ):
        raise TypeError(
            "spatial boundary composition requires canonical transfer pairs"
        )
    # Validate every handle before constructing any semantic node.  This keeps
    # foreign and integer-aliased IDs out of warm as well as cold operations.
    for item in (first, second):
        _validate_endomorphism(structures, item.left, left_port)
        _validate_endomorphism(structures, item.right, right_port)
        product = structures.resolve(item.product)
        if product.kind != "product" or product.components != (item.left, item.right):
            raise ValueError("boundary transfer product disagrees with its components")
    left = compose_endomorphisms(structures, first.left, second.left, left_port)
    right = compose_endomorphisms(structures, second.right, first.right, right_port)
    return boundary_transfer(structures, left, right, left_port, right_port)


def apply_endomorphism(
    structures: StructureArena,
    function: StructureID,
    port: FinitePort,
    state: int,
) -> int:
    """Test/oracle observation of one canonical finite boundary function."""
    if type(state) is not int or not 0 <= state < port.cardinality:
        raise ValueError("boundary state lies outside its finite domain")
    _validate_endomorphism(structures, function, port)
    sort = AtomSort(port.variable.role, port.cardinality)
    argument = structures.bits.constant(FunctionSignature((), sort), state)
    result = structures.apply(function, {port.variable: argument})
    observed = structures.evaluate_atom(result, {})
    if type(observed) is not int:
        raise ValueError("total boundary transfer returned an invalid state")
    return observed


__all__ = [
    "HigherBoundaryTransfer",
    "HigherSpatialWiring",
    "StructuredBoundaryTransfer",
    "apply_endomorphism",
    "boundary_endomorphism",
    "boundary_transfer",
    "compose_endomorphisms",
    "compose_higher_spatial_transfers",
    "compose_higher_spatial_wiring",
    "compose_spatial_transfers",
    "higher_boundary_transfer",
]
