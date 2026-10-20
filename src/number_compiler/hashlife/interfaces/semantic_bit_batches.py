"""Transactional multi-root operations for one finite Boolean circuit."""

from __future__ import annotations

from collections.abc import Callable, Mapping

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.boolean_composition import (
    substitute_boolean_fused,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    BitSubstitutionKey,
    BooleanCircuit,
    FactoredFunction,
    FactoredFunctionID,
    PendingFunction,
    substitute_boolean,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)


def divmod_atoms(
    arena: BitFunctionArena,
    function: FactoredFunctionID,
    divisor: int,
    quotient_sort: AtomSort,
    remainder_sort: AtomSort,
) -> tuple[FactoredFunctionID, FactoredFunctionID]:
    """Restoring binary division, sharing the existing carry/subtraction DAG."""
    source = arena.resolve(function)
    domain = source.signature.output
    if type(divisor) is not int or not 1 <= divisor <= 1 << 63:
        raise ValueError("atom divisor must be in 1..2**63")
    if (
        type(domain) is not AtomSort
        or type(quotient_sort) is not AtomSort
        or type(remainder_sort) is not AtomSort
        or quotient_sort.cardinality != (domain.cardinality - 1) // divisor + 1
        or remainder_sort.cardinality != divisor
    ):
        raise ValueError("atom division has incompatible quotient/remainder sorts")
    circuit = BooleanCircuit(arena.functions, source.signature.inputs)
    bits, valid = circuit.imported(source)
    width = (divisor - 1).bit_length()
    remainder = (circuit.zero,) * width
    quotient: list[int] = []
    for bit in reversed(bits):
        doubled = (bit, *remainder)
        difference, borrow = circuit.subtract_constant(doubled, divisor)
        take = circuit.negate(borrow)
        remainder = tuple(
            circuit.choose(take, difference[i], doubled[i]) for i in range(width)
        )
        quotient.append(take)
    count = (quotient_sort.cardinality - 1).bit_length()
    quot = circuit.normalized(
        FunctionSignature(source.signature.inputs, quotient_sort),
        tuple(reversed(quotient))[:count],
        valid,
    )
    rem = circuit.normalized(
        FunctionSignature(source.signature.inputs, remainder_sort),
        remainder,
        valid,
    )
    result = arena.publish_circuit(circuit, (quot, rem))
    arena.ledger.bump(_interfaces_keys.SEMANTIC_ATOM_DIVISION_BITS, len(bits))
    return result[0], result[1]


def substitute_many(
    arena: BitFunctionArena,
    functions: tuple[FactoredFunctionID, ...],
    replacements: Mapping[PortVariable, FactoredFunctionID],
    *,
    joint: bool,
) -> tuple[FactoredFunctionID, ...]:
    """Substitute one environment through several roots in one transaction.

    Every result keeps the same evictable per-root substitution key as the
    scalar operation. A fully warm batch returns before opening a transaction.
    """
    if type(functions) is not tuple or not functions:
        raise ValueError("batch substitution requires immutable nonempty roots")
    if type(joint) is not bool:
        raise TypeError("substitution strategy requires a Boolean flag")
    originals = tuple(arena.resolve(function) for function in functions)
    source_inputs = originals[0].signature.inputs
    if any(node.signature.inputs != source_inputs for node in originals[1:]):
        raise ValueError("batch substitution requires one complete input interface")
    items, references = admitted_replacements(arena, source_inputs, replacements)
    if not items:
        return functions
    ordered_references = tuple(sorted(references))
    keys = tuple(
        BitSubstitutionKey(function, ordered_references) for function in functions
    )
    cached = tuple(arena.lookup_composition(key) for key in keys)
    hit_count = sum(result is not None for result in cached)
    arena.ledger.bump(
        _interfaces_keys.SEMANTIC_BIT_COMPOSITION_REQUESTS, len(functions)
    )
    arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_COMPOSITION_HITS, hit_count)
    if all(result is not None for result in cached):
        resolved = tuple(result for result in cached if result is not None)
        arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_BATCH_COMPOSITION_HITS)
        return resolved
    seen: set[BitSubstitutionKey] = set()
    missing_list: list[int] = []
    for index, (key, result) in enumerate(zip(keys, cached, strict=True)):
        if result is None and key not in seen:
            seen.add(key)
            missing_list.append(index)
    missing = tuple(missing_list)
    removed = {port.variable for port, _ in items}
    inputs = union_inputs(
        tuple(port for port in source_inputs if port.variable not in removed),
        *(value.signature.inputs for _, value in items),
    )
    circuit = BooleanCircuit(arena.functions, inputs)
    try:
        mapping, replacement_valid, transform = substitution_environment(
            circuit, items, joint
        )
        pending: list[PendingFunction] = []
        for index in missing:
            original = originals[index]
            bits = tuple(
                transform(circuit, bit.local_id, mapping) for bit in original.bits
            )
            valid = transform(circuit, original.valid.local_id, mapping)
            pending.append(
                circuit.normalized(
                    FunctionSignature(inputs, original.signature.output),
                    bits,
                    circuit.conjunction(replacement_valid, valid),
                )
            )
        arena.ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_COMPOSITION_EVALUATIONS,
            len(missing),
        )
        arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_BATCH_COMPOSITION_EVALUATIONS)
        published = arena.publish_circuit(
            circuit,
            tuple(pending),
            substitutions=tuple(keys[index] for index in missing),
        )
        by_key = dict(zip((keys[index] for index in missing), published, strict=True))
        return tuple(
            by_key[key] if result is None else result
            for key, result in zip(keys, cached, strict=True)
        )
    except BaseException:
        circuit.tx.close()
        raise


def restrict_many(
    arena: BitFunctionArena,
    functions: tuple[FactoredFunctionID, ...],
    predicate: FactoredFunctionID,
) -> tuple[FactoredFunctionID, ...]:
    """Restrict several roots under one complete-interface predicate."""
    if type(functions) is not tuple or not functions:
        raise ValueError("batch restriction requires immutable nonempty roots")
    values = tuple(arena.resolve(function) for function in functions)
    guard = arena.resolve(predicate)
    if guard.signature.output != BOOL:
        raise ValueError("function restriction requires a Boolean predicate")
    inputs = guard.signature.inputs
    allowed: set[FinitePort] = set(inputs)
    if any(not set(value.signature.inputs) <= allowed for value in values):
        raise ValueError("batch restriction has an undeclared input port")
    circuit = BooleanCircuit(arena.functions, inputs)
    try:
        condition, admitted = circuit.imported(guard)
        pending: list[PendingFunction] = []
        for value in values:
            bits, valid = circuit.imported(value)
            pending.append(
                circuit.normalized(
                    FunctionSignature(inputs, value.signature.output),
                    bits,
                    circuit.conjunction(
                        valid,
                        circuit.conjunction(admitted, condition[0]),
                    ),
                )
            )
        arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_BATCH_RESTRICTION_EVALUATIONS)
        return arena.publish_circuit(circuit, tuple(pending))
    except BaseException:
        circuit.tx.close()
        raise


__all__ = ["restrict_many", "substitute_many"]


def admitted_replacements(
    arena: BitFunctionArena,
    source_inputs: tuple[FinitePort, ...],
    replacements: Mapping[PortVariable, FactoredFunctionID],
) -> tuple[
    list[tuple[FinitePort, FactoredFunction]],
    list[tuple[PortVariable, FactoredFunctionID]],
]:
    """Validate the same complete finite domain for scalar and batch substitution."""
    admitted = {port.variable: port for port in source_inputs}
    items: list[tuple[FinitePort, FactoredFunction]] = []
    references: list[tuple[PortVariable, FactoredFunctionID]] = []
    for variable, reference in replacements.items():
        if type(variable) is not PortVariable:
            raise ValueError("substitution needs typed finite port names")
        PortVariable.__post_init__(variable)
        port = admitted.get(variable)
        replacement = arena.resolve(reference)
        if (
            port is None
            or type(replacement.signature.output) is not AtomSort
            or replacement.signature.output.cardinality != port.cardinality
        ):
            raise ValueError("substitution changes a finite input domain")
        items.append((port, replacement))
        references.append((variable, reference))
    items.sort(key=lambda item: item[0].variable)
    return items, references


def substitution_environment(
    circuit: BooleanCircuit,
    items: list[tuple[FinitePort, FactoredFunction]],
    joint: bool,
) -> tuple[
    dict[PortVariable, int],
    int,
    Callable[[BooleanCircuit, int, Mapping[PortVariable, int]], int],
]:
    """Import one correlated argument environment and select its cofactor engine."""
    mapping: dict[PortVariable, int] = {}
    replacement_valid = circuit.admitted()
    for port, value in items:
        bits, valid = circuit.imported(value)
        replacement_valid = circuit.conjunction(replacement_valid, valid)
        for bit, root in enumerate(bits):
            mapping[
                PortVariable(
                    port.variable.time,
                    port.variable.side,
                    port.variable.role,
                    bit,
                )
            ] = root
    fused = joint and any(
        len(circuit.tx.node(value).support) > 1 for value in mapping.values()
    )
    transform = substitute_boolean_fused if fused else substitute_boolean
    return mapping, replacement_valid, transform
