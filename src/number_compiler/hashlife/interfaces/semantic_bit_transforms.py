"""Complete finite-interface saturation using the existing Boolean DAG owner.

These records are arithmetic functions, not source admissions or recursive
spatial constructors. Extra retained consumers participate in the same domain,
substitution and restriction transaction; they never become successor inputs.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)


@dataclass(frozen=True, slots=True)
class CompleteFiniteTransform:
    """Canonical outputs and their joint admission; no duration or provenance."""

    ports: tuple[FinitePort, ...]
    outputs: tuple[FactoredFunctionID, ...]
    admissible: FactoredFunctionID


def normalize(
    arena: BitFunctionArena,
    ports: tuple[FinitePort, ...],
    outputs: tuple[FactoredFunctionID, ...],
    admissible: FactoredFunctionID,
    retained: tuple[FactoredFunctionID, ...],
) -> tuple[CompleteFiniteTransform, tuple[FactoredFunctionID, ...]]:
    FunctionSignature(ports, BOOL)
    if type(outputs) is not tuple or type(retained) is not tuple:
        raise TypeError("complete transform functions must be immutable tuples")
    if not ports or len(outputs) != len(ports):
        raise ValueError("complete transform needs one output per input port")
    if arena.resolve(admissible).signature.output != BOOL:
        raise ValueError("complete transform admission must be Boolean")
    allowed = set(ports)
    for port, function in zip(ports, outputs, strict=True):
        output = arena.resolve(function).signature.output
        if type(output) is not AtomSort or output.cardinality != port.cardinality:
            raise ValueError("complete transform changes an input port sort")
    for function in (admissible, *outputs, *retained):
        if not set(arena.resolve(function).signature.inputs) <= allowed:
            raise ValueError("complete transform contains an undeclared context port")
    false = arena.constant(FunctionSignature((), BOOL), 0)
    full = arena.constant(FunctionSignature(ports, BOOL), 1)
    # Undefined and false guards both reject the source. Publish their truth
    # set as a total predicate on the declared port domain; retaining guard
    # definedness would give the same partial transformation two identities.
    admitted = arena.select(full, admissible, false)
    if arena.resolve(admitted).valid != arena.resolve(full).valid:
        admitted = arena.select(arena.domain_predicate(admitted), admitted, false)
    for function in (*outputs, *retained):
        admitted = arena.select(admitted, arena.domain_predicate(function), false)
    restricted = arena.restrict_many((*outputs, *retained), admitted)
    count = len(outputs)
    return CompleteFiniteTransform(ports, restricted[:count], admitted), restricted[
        count:
    ]


def validate(arena: BitFunctionArena, transform: CompleteFiniteTransform) -> None:
    if type(transform) is not CompleteFiniteTransform:
        raise TypeError("expected a complete finite transform")
    FunctionSignature(transform.ports, BOOL)
    if (
        type(transform.outputs) is not tuple
        or not transform.ports
        or len(transform.outputs) != len(transform.ports)
    ):
        raise ValueError("incomplete finite transform")
    admitted = arena.resolve(transform.admissible)
    if admitted.signature != FunctionSignature(transform.ports, BOOL):
        raise ValueError("complete transform admission has another context")
    full = arena.resolve(arena.constant(admitted.signature, 1))
    if admitted.valid != full.valid:
        raise ValueError("complete transform admission must be total on its ports")
    for port, function in zip(transform.ports, transform.outputs, strict=True):
        node = arena.resolve(function)
        if (
            node.signature.inputs != transform.ports
            or type(node.signature.output) is not AtomSort
            or node.signature.output.cardinality != port.cardinality
            or node.valid != admitted.bits[0]
        ):
            raise ValueError(
                "complete transform output has inconsistent context or domain"
            )


def compose(
    arena: BitFunctionArena,
    before: CompleteFiniteTransform,
    after: CompleteFiniteTransform,
    retained: tuple[FactoredFunctionID, ...],
) -> tuple[CompleteFiniteTransform, tuple[FactoredFunctionID, ...]]:
    validate(arena, before)
    validate(arena, after)
    if before.ports != after.ports:
        raise ValueError("complete transforms require the same transported interface")
    if type(retained) is not tuple:
        raise TypeError("retained consumers must be an immutable tuple")
    admitted_after = arena.resolve(after.admissible)
    for function in retained:
        node = arena.resolve(function)
        if node.signature.inputs != after.ports or node.valid != admitted_after.bits[0]:
            raise ValueError("retained consumer has another context or domain")
    mapping = dict(
        zip((port.variable for port in before.ports), before.outputs, strict=True)
    )
    pulled = arena.substitute_many(
        (after.admissible, *after.outputs, *retained), mapping
    )
    false = arena.constant(FunctionSignature((), BOOL), 0)
    admitted = arena.select(before.admissible, pulled[0], false)
    count = len(after.outputs)
    return normalize(
        arena, before.ports, pulled[1 : 1 + count], admitted, pulled[1 + count :]
    )
