"""Validation of one retained higher runtime-value record."""

from __future__ import annotations

from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeContextState,
    RuntimeFunction,
    RuntimePair,
    RuntimeRecord,
    RuntimeSummaryFunction,
    RuntimeTableFunction,
    RuntimeTransferredState,
    RuntimeValueArena,
    RuntimeValueID,
)


def valid_runtime_value_record(
    arena: RuntimeValueArena,
    semantics: HigherSemanticArena | None,
    record: RuntimeRecord,
) -> bool:
    """Validate one record through all scoped owners it references."""
    if type(record) is RuntimeFunction:
        if type(record.environment) is not int or record.environment < -1:
            return False
        arena.validate_function(record.function)
        if record.environment >= 0:
            arena.environment(record.environment)
        return True
    if type(record) is RuntimeActionFunction:
        if (
            type(record.kind) is not str
            or record.kind not in ("constant", "step")
            or type(record.side) is not int
            or record.side not in (0, 1)
            or type(record.symbol) is not int
        ):
            return False
        arena.validate_atom(record.anchor)
        if semantics is None:
            return False
        schema = semantics.schema
        schema.validate_action(record.action)
        children = schema.children(record.action)
        if children is None:
            return False
        if record.kind == "constant":
            if record.continuation is not None or record.symbol != -1:
                return False
            expected = children[1]
        else:
            _base, blank = schema.alphabet(record.action)
            if (
                type(blank) is not int
                or not 0 <= record.symbol <= blank
                or type(record.continuation) is not RuntimeValueID
                or type(arena.resolve(record.continuation))
                not in (
                    RuntimeFunction,
                    RuntimeActionFunction,
                    RuntimeTableFunction,
                    RuntimeSummaryFunction,
                )
            ):
                return False
            expected = children[0]
        try:
            arena.validate_action_atom(expected, record.side, record.anchor)
        except (TypeError, ValueError):
            return False
        return True
    if type(record) is RuntimeTableFunction:
        if semantics is None:
            return False
        if (
            type(record.side) is not int
            or record.side not in (0, 1)
            or type(record.outputs) is not tuple
            or not record.outputs
            or any(type(value) is not int for value in record.outputs)
        ):
            return False
        schema = semantics.schema
        schema.validate_action(record.action)
        children = schema.children(record.action)
        if children is None or any(
            schema.children(child) is not None for child in children
        ):
            return False
        domain = schema.state_count(children[0], 1 - record.side)
        codomain = schema.state_count(children[1], record.side)
        return (
            type(domain) is int
            and type(codomain) is int
            and 1 <= domain <= 64
            and 1 <= codomain <= 1 << 64
            and len(record.outputs) == domain
            and all(0 <= value < codomain for value in record.outputs)
        )
    if type(record) is RuntimeTransferredState:
        arena.validate_summary(record.summary, kind="unary")
        arena.validate_atom(record.incoming)
        return True
    if type(record) is RuntimeContextState:
        arena.validate_summary(record.summary, kind="context")
        for atom in (record.left, record.right, record.incoming):
            arena.validate_atom(atom)
        return type(record.side) is int and record.side in (0, 1)
    if type(record) is RuntimeSummaryFunction:
        arena.validate_summary(record.context, kind="context")
        arena.validate_summary(record.opposite, kind="unary")
        arena.validate_atom(record.anchor)
        arena.resolve(record.continuation)
        return type(record.side) is int and record.side in (0, 1)
    if type(record) is RuntimePair:
        arena.validate_atom(record.anchor)
        return type(arena.resolve(record.continuation)) in (
            RuntimeFunction,
            RuntimeActionFunction,
            RuntimeTableFunction,
            RuntimeSummaryFunction,
        )
    return False


__all__ = ["valid_runtime_value_record"]
