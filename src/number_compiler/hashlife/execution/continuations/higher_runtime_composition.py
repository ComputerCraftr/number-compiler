"""Iterative spatial/temporal interchange for canonical runtime K summaries.

K inputs are in scan order. U children always remain in physical low/high
order, including for a backward K. No midpoint symbols are evaluated here.
"""

from __future__ import annotations

from number_compiler.hashlife.execution.continuations.higher_summaries import (
    ContextSpatial,
    HigherSummaryArena,
    HigherSummaryID,
    RuntimeContextSummary,
    RuntimeUnarySummary,
    UnaryAffine,
    UnaryFinite,
    UnaryIdentity,
    UnarySpatial,
    UnaryTemporal,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


def _pair(
    arena: HigherSummaryArena,
    first: HigherSummaryID,
    second: HigherSummaryID,
) -> tuple[RuntimeUnarySummary, RuntimeUnarySummary]:
    a, b = arena.runtime_unary_record(first), arena.runtime_unary_record(second)
    if (a.action, a.side) != (b.action, b.side):
        raise ValueError("runtime spatial summaries have incompatible interfaces")
    return a, b


def _publish(
    arena: HigherSummaryArena,
    key: tuple[HigherSummaryID, HigherSummaryID],
    record: RuntimeUnarySummary,
    *,
    context: RuntimeContextSummary | None = None,
) -> HigherSummaryID:
    """Reserve the complete parent, its context, and its binding together."""
    found = arena._keys.get(record)
    context_new = context is not None and context not in arena._keys
    charges = [(arena._runtime_composition_owner, 1, 0)]
    if found is None:
        charges.extend(((arena._node_owner, 1, 1), (arena._key_owner, 1, 0)))
    if context_new:
        charges.extend(((arena._node_owner, 1, 1), (arena._key_owner, 1, 0)))
    arena.ledger.reserve_many(charges)
    if context_new:
        assert context is not None
        local_id = len(arena._nodes)
        arena._nodes.append(context)
        arena._keys[context] = local_id
        arena.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_PUBLICATIONS)
    elif context is not None:
        arena.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_HITS)
    if found is None:
        found = len(arena._nodes)
        arena._nodes.append(record)
        arena._keys[record] = found
        arena.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_PUBLICATIONS)
    else:
        arena.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_HITS)
    result = arena._handle(found, record)
    arena._runtime_compositions[key] = result
    return result


def compose_runtime_pair(
    arena: HigherSummaryArena,
    first: HigherSummaryID,
    second: HigherSummaryID,
) -> HigherSummaryID:
    """Apply first, then second; normalize before semantic publication."""
    a, b = _pair(arena, first, second)
    if type(a.recipe) is UnaryIdentity or type(b.recipe) is UnaryIdentity:
        arena.ledger.bump(_execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS)
        return second if type(a.recipe) is UnaryIdentity else first
    root = first, second
    stack = [(root, False)]
    while stack:
        key, ready = stack.pop()
        arena.ledger.bump(_execution_keys.HIGHER_RUNTIME_COMPOSITION_REQUESTS)
        if key in arena._runtime_compositions:
            arena.ledger.bump(_execution_keys.HIGHER_RUNTIME_COMPOSITION_HITS)
            continue
        a, b = _pair(arena, *key)
        x, y = a.recipe, b.recipe
        if type(x) is UnaryIdentity or type(y) is UnaryIdentity:
            chosen = b if type(x) is UnaryIdentity else a
            _publish(arena, key, chosen)
            arena.ledger.bump(_execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS)
            continue
        if type(x) is UnaryAffine and type(y) is UnaryAffine:
            transfer = x.transfer.then(y.transfer, arena.ledger)
            _publish(
                arena, key, RuntimeUnarySummary(a.action, a.side, UnaryAffine(transfer))
            )
            continue
        if type(x) is UnaryFinite and type(y) is UnaryFinite:
            outputs = tuple(y.outputs[state] for state in x.outputs)
            arena.ledger.bump(_execution_keys.HIGHER_FINITE_TRANSFER_COMPOSITIONS)
            arena.ledger.bump(
                _execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS,
                len(outputs),
            )
            _publish(
                arena,
                key,
                RuntimeUnarySummary(
                    a.action,
                    a.side,
                    UnaryIdentity()
                    if outputs == tuple(range(len(outputs)))
                    else UnaryFinite(outputs),
                ),
            )
            continue
        if type(x) is not UnaryTemporal or type(y) is not UnaryTemporal:
            _publish(
                arena, key, RuntimeUnarySummary(a.action, a.side, UnarySpatial(*key))
            )
            continue
        forward = x.forward, y.forward
        opposite = y.opposite, x.opposite
        if not ready:
            stack.append((key, True))
            stack.extend((dependency, False) for dependency in (opposite, forward))
            continue
        u, v = (
            arena.runtime_context_record(x.context),
            arena.runtime_context_record(y.context),
        )
        if (u.provider, u.consumer) != (v.provider, v.consumer):
            raise ValueError("temporal contexts have incompatible interfaces")
        geometry = (
            ContextSpatial(x.context, y.context, x.forward, y.opposite)
            if a.side == 0
            else ContextSpatial(y.context, x.context, y.opposite, x.forward)
        )
        context_record = RuntimeContextSummary(u.provider, u.consumer, geometry)
        # A prospective ID is private until the joint reservation succeeds.
        # Never retain the context first and then discover that the parent
        # binding cannot fit its budget.
        context_id = arena._keys.get(context_record, len(arena._nodes))
        context = arena._handle(context_id, context_record)
        _publish(
            arena,
            key,
            RuntimeUnarySummary(
                a.action,
                a.side,
                UnaryTemporal(
                    arena._runtime_compositions[forward],
                    arena._runtime_compositions[opposite],
                    context,
                ),
            ),
            context=context_record,
        )
        arena.ledger.bump(_execution_keys.HIGHER_RUNTIME_INTERCHANGE_COMPOSITIONS)
    return arena._runtime_compositions[root]
