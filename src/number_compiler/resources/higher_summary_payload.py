"""Independent validation for retained higher K/U summary DAGs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from number_compiler.hashlife.execution.continuations.higher_summaries import (
    ContextLeaf,
    ContextSpatial,
    ContextSummary,
    HigherSummaryArena,
    HigherSummaryID,
    RuntimeContextSummary,
    RuntimeUnarySummary,
    UnaryAffine,
    UnaryFinite,
    UnaryIdentity,
    UnaryLeaf,
    UnarySpatial,
    UnarySummary,
    UnaryTemporal,
    _ContextBinding,
    _UnaryBinding,
)
from number_compiler.resources.ledger import ResourceLedger


def _identity_index(mapping: object, record: object, index: int) -> bool:
    try:
        found = mapping.get(record)  # type: ignore[attr-defined]
        return type(found) is int and found == index
    except (KeyError, TypeError, AttributeError):
        return any(
            key is record and type(value) is int and value == index
            for key, value in mapping.items()  # type: ignore[attr-defined]
        )


def _summary_reference(
    arena: HigherSummaryArena,
    reference: HigherSummaryID,
    before: int,
    *,
    unary: bool,
    runtime: bool,
) -> bool:
    if type(reference) is not HigherSummaryID or not 0 <= reference.local_id < before:
        return False
    record = arena.resolve(reference)
    expected = (
        RuntimeUnarySummary
        if unary and runtime
        else UnarySummary
        if unary
        else RuntimeContextSummary
        if runtime
        else ContextSummary
    )
    return type(record) is expected


def _recipe(
    arena: HigherSummaryArena,
    recipe: object,
    before: int,
    *,
    unary: bool,
    runtime: bool,
) -> bool:
    if unary:
        if type(recipe) is UnaryIdentity:
            return True
        if type(recipe) is UnaryAffine:
            from number_compiler.arithmetic.radix_transfer import (
                RadixRemainderTransfer,
            )

            if type(recipe.transfer) is not RadixRemainderTransfer:
                return False
            recipe.transfer.__post_init__()
            return runtime
        if type(recipe) is UnaryFinite:
            recipe.__post_init__()
            return runtime
        if type(recipe) is UnaryLeaf:
            return type(recipe.symbol) is int and recipe.symbol >= 0
        if type(recipe) is UnarySpatial:
            return _summary_reference(
                arena,
                recipe.first,
                before,
                unary=True,
                runtime=runtime,
            ) and _summary_reference(
                arena,
                recipe.second,
                before,
                unary=True,
                runtime=runtime,
            )
        if type(recipe) is UnaryTemporal:
            return all(
                (
                    _summary_reference(
                        arena,
                        recipe.forward,
                        before,
                        unary=True,
                        runtime=runtime,
                    ),
                    _summary_reference(
                        arena,
                        recipe.opposite,
                        before,
                        unary=True,
                        runtime=runtime,
                    ),
                    _summary_reference(
                        arena,
                        recipe.context,
                        before,
                        unary=False,
                        runtime=runtime,
                    ),
                )
            )
        return False
    if type(recipe) is ContextLeaf:
        return type(recipe.symbol) is int and recipe.symbol >= 0
    if type(recipe) is ContextSpatial:
        return all(
            (
                _summary_reference(
                    arena,
                    recipe.low,
                    before,
                    unary=False,
                    runtime=runtime,
                ),
                _summary_reference(
                    arena,
                    recipe.high,
                    before,
                    unary=False,
                    runtime=runtime,
                ),
                _summary_reference(
                    arena,
                    recipe.low_forward,
                    before,
                    unary=True,
                    runtime=runtime,
                ),
                _summary_reference(
                    arena,
                    recipe.high_backward,
                    before,
                    unary=True,
                    runtime=runtime,
                ),
            )
        )
    return False


def _composition_result(
    arena: HigherSummaryArena,
    key: tuple[HigherSummaryID, HigherSummaryID],
    first: RuntimeUnarySummary,
    second: RuntimeUnarySummary,
    output: RuntimeUnarySummary,
) -> bool:
    """Check the publication equation without executing or mutating the arena."""
    x, y, result = first.recipe, second.recipe, output.recipe
    if type(x) is UnaryIdentity or type(y) is UnaryIdentity:
        return output == (second if type(x) is UnaryIdentity else first)
    if type(x) is UnaryFinite and type(y) is UnaryFinite:
        expected = tuple(y.outputs[state] for state in x.outputs)
        return result == (
            UnaryIdentity()
            if expected == tuple(range(len(expected)))
            else UnaryFinite(expected)
        )
    if type(x) is UnaryAffine and type(y) is UnaryAffine:
        # Audit arithmetic concerns two bounded coefficients only. It never
        # evaluates a field, a temporal exponent, or an output prefix.
        a, b = x.transfer, y.transfer
        return type(result) is UnaryAffine and (
            a.radix == b.radix == result.transfer.radix
            and result.transfer.multiplier == b.multiplier * a.multiplier % a.radix
            and result.transfer.offset == (b.multiplier * a.offset + b.offset) % a.radix
        )
    if type(x) is not UnaryTemporal or type(y) is not UnaryTemporal:
        return result == UnarySpatial(*key)
    if type(result) is not UnaryTemporal:
        return False
    forward = arena._runtime_compositions.get((x.forward, y.forward))
    opposite = arena._runtime_compositions.get((y.opposite, x.opposite))
    u = arena.runtime_context_record(x.context)
    v = arena.runtime_context_record(y.context)
    context = arena.runtime_context_record(result.context)
    geometry = (
        ContextSpatial(x.context, y.context, x.forward, y.opposite)
        if first.side == 0
        else ContextSpatial(y.context, x.context, y.opposite, x.forward)
    )
    return (
        (u.provider, u.consumer)
        == (v.provider, v.consumer)
        == (context.provider, context.consumer)
        and context.recipe == geometry
        and (result.forward, result.opposite) == (forward, opposite)
    )


def audit_higher_summary_arena(
    arena: HigherSummaryArena,
    ledger: ResourceLedger,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate summary nodes, bindings, and memo ownership without execution."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    stores = (
        (arena._node_owner, arena._nodes),
        (arena._key_owner, arena._keys),
        (arena._binding_owner, arena._bindings),
        (arena._runtime_binding_owner, arena._runtime_bindings),
        (arena._blank_identity_owner, arena._blank_identity),
        (arena._runtime_composition_owner, arena._runtime_compositions),
    )
    valid_root = (
        arena.ledger is ledger
        and arena.semantics.ledger is ledger
        and arena.sources.ledger is ledger
        and arena.schema is arena.semantics.schema
        and all(containers.get(owner) is value for owner, value in stores)
    )
    nodes_valid = valid_root
    for index, record in enumerate(arena._nodes):
        valid = valid_root and type(record) in (
            UnarySummary,
            ContextSummary,
            RuntimeUnarySummary,
            RuntimeContextSummary,
        )
        try:
            runtime = type(record) in (RuntimeUnarySummary, RuntimeContextSummary)
            unary = type(record) in (UnarySummary, RuntimeUnarySummary)
            if unary:
                unary_item = cast(UnarySummary | RuntimeUnarySummary, record)
                arena.schema.validate_action(unary_item.action)
                valid &= type(unary_item.side) is int and unary_item.side in (0, 1)
                if type(unary_item.recipe) is UnaryAffine:
                    valid &= (
                        unary_item.recipe.transfer.radix
                        == arena.schema.state_count(
                            unary_item.action,
                            unary_item.side,
                        )
                    )
                if type(unary_item.recipe) is UnaryFinite:
                    valid &= len(unary_item.recipe.outputs) == arena.schema.state_count(
                        unary_item.action,
                        unary_item.side,
                    )
                if type(unary_item) is UnarySummary:
                    function = arena.semantics.function_record(unary_item.function)
                    state = arena.semantics.state_sort(
                        unary_item.action,
                        unary_item.side,
                    )
                    valid &= (
                        function.signature.domain
                        == function.signature.codomain
                        == state
                    )
            else:
                context_item = cast(ContextSummary | RuntimeContextSummary, record)
                arena.schema.validate_action(context_item.provider)
                arena.schema.validate_action(context_item.consumer)
                if type(context_item) is ContextSummary:
                    expressions = (
                        context_item.left,
                        context_item.right,
                        context_item.incoming_left,
                        context_item.incoming_right,
                        context_item.left_body,
                        context_item.right_body,
                    )
                    tuple(arena.semantics.expression(value) for value in expressions)
            valid &= _recipe(
                arena,
                record.recipe,
                index,
                unary=unary,
                runtime=runtime,
            )
            valid &= arena.resolve(arena._handle(index, record)) is record
            valid &= _identity_index(arena._keys, record, index)
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.update((id(record), id(record.recipe)))
        else:
            invalid.add((arena._node_owner, id(record)))
            nodes_valid = False

    bindings_valid = valid_root
    for bindings, runtime, owner in (
        (arena._bindings, False, arena._binding_owner),
        (arena._runtime_bindings, True, arena._runtime_binding_owner),
    ):
        for binding, result in bindings.items():
            valid = type(binding) in (_UnaryBinding, _ContextBinding)
            try:
                if type(result) is not HigherSummaryID:
                    raise TypeError("invalid higher summary binding result")
                record = arena.resolve(result)
                expected = (
                    RuntimeUnarySummary
                    if type(binding) is _UnaryBinding and runtime
                    else UnarySummary
                    if type(binding) is _UnaryBinding
                    else RuntimeContextSummary
                    if runtime
                    else ContextSummary
                )
                valid &= type(record) is expected
                if type(binding) is _UnaryBinding:
                    arena.schema.validate_action(binding.action)
                    arena.validate_input(binding.source)
                    valid &= type(binding.side) is int and binding.side in (0, 1)
                    if type(record) in (UnarySummary, RuntimeUnarySummary):
                        unary_record = cast(UnarySummary | RuntimeUnarySummary, record)
                        valid &= (unary_record.action, unary_record.side) == (
                            binding.action,
                            binding.side,
                        )
                else:
                    context_binding = cast(_ContextBinding, binding)
                    arena.schema.validate_action(context_binding.provider)
                    arena.schema.validate_action(context_binding.consumer)
                    arena.validate_input(context_binding.source)
                    if type(record) in (ContextSummary, RuntimeContextSummary):
                        context_record = cast(
                            ContextSummary | RuntimeContextSummary,
                            record,
                        )
                        valid &= (context_record.provider, context_record.consumer) == (
                            context_binding.provider,
                            context_binding.consumer,
                        )
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.update((id(binding), id(result)))
            else:
                invalid.add((owner, id(binding)))
                bindings_valid = False

    blank_valid = valid_root
    for key, value in arena._blank_identity.items():
        valid = type(key) is tuple and len(key) == 2 and type(value) is bool
        try:
            action, side = key
            arena.schema.validate_action(action)
            valid &= type(side) is int and side in (0, 1)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.add(id(key))
        else:
            invalid.add((arena._blank_identity_owner, id(key)))
            blank_valid = False
    compositions_valid = valid_root
    for composition_key, result in arena._runtime_compositions.items():
        valid = type(composition_key) is tuple and len(composition_key) == 2
        try:
            if not valid:
                raise ValueError("invalid runtime composition composition_key")
            first, second = (
                arena.runtime_unary_record(item) for item in composition_key
            )
            output = arena.runtime_unary_record(result)
            valid &= (first.action, first.side) == (second.action, second.side)
            valid &= (first.action, first.side) == (output.action, output.side)
            valid &= _composition_result(arena, composition_key, first, second, output)
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.add(id(composition_key))
        else:
            invalid.add((arena._runtime_composition_owner, id(composition_key)))
            compositions_valid = False
    if nodes_valid and bindings_valid and blank_valid and compositions_valid:
        approved.update(id(value) for _, value in stores)
    return approved, invalid


__all__ = ["audit_higher_summary_arena"]
