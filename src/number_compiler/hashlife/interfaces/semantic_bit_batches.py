"""Transactional multi-root operations for one finite Boolean circuit."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FunctionSignature,
    _union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.boolean_composition import (
    substitute_boolean_fused,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
    _Circuit,
    substitute_boolean,
)


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
    admitted = {port.variable: port for port in source_inputs}
    items = []
    references = []
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
    if not items:
        return functions
    from number_compiler.hashlife.interfaces.semantic_bits import BitSubstitutionKey

    ordered_references = tuple(sorted(references))
    keys = tuple(
        BitSubstitutionKey(function, ordered_references) for function in functions
    )
    cached = tuple(arena._compositions.get(key) for key in keys)
    for result in cached:
        if result is not None:
            arena.resolve(result)
    hit_count = sum(result is not None for result in cached)
    arena.ledger.bump("semantic_bit_composition_requests", len(functions))
    arena.ledger.bump("semantic_bit_composition_hits", hit_count)
    if all(result is not None for result in cached):
        resolved = tuple(result for result in cached if result is not None)
        arena.ledger.bump("semantic_bit_batch_composition_hits")
        return resolved
    seen = set()
    missing_list = []
    for index, (key, result) in enumerate(zip(keys, cached, strict=True)):
        if result is None and key not in seen:
            seen.add(key)
            missing_list.append(index)
    missing = tuple(missing_list)
    removed = {port.variable for port, _ in items}
    inputs = _union_inputs(
        tuple(port for port in source_inputs if port.variable not in removed),
        *(value.signature.inputs for _, value in items),
    )
    circuit = _Circuit(arena.functions, inputs)
    try:
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
        pending = []
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
        arena.ledger.bump("semantic_bit_composition_evaluations", len(missing))
        arena.ledger.bump("semantic_bit_batch_composition_evaluations")
        published = arena._publish(
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
    allowed = set(inputs)
    if any(not set(value.signature.inputs) <= allowed for value in values):
        raise ValueError("batch restriction has an undeclared input port")
    circuit = _Circuit(arena.functions, inputs)
    try:
        condition, admitted = circuit.imported(guard)
        pending = []
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
        arena.ledger.bump("semantic_bit_batch_restriction_evaluations")
        return arena._publish(circuit, tuple(pending))
    except BaseException:
        circuit.tx.close()
        raise


__all__ = ["restrict_many", "substitute_many"]
