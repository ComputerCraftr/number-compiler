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
        if key in arena.runtime_compositions:
            arena.ledger.bump(_execution_keys.HIGHER_RUNTIME_COMPOSITION_HITS)
            continue
        a, b = _pair(arena, *key)
        x, y = a.recipe, b.recipe
        if type(x) is UnaryIdentity or type(y) is UnaryIdentity:
            chosen = b if type(x) is UnaryIdentity else a
            arena.publish_runtime_composition(key, chosen)
            arena.ledger.bump(_execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS)
            continue
        if type(x) is UnaryAffine and type(y) is UnaryAffine:
            transfer = x.transfer.then(y.transfer, arena.ledger)
            arena.publish_runtime_composition(
                key, RuntimeUnarySummary(a.action, a.side, UnaryAffine(transfer))
            )
            continue
        if type(x) is UnaryFinite and type(y) is UnaryFinite:
            outputs = tuple(y.outputs[state] for state in x.outputs)
            arena.ledger.bump(_execution_keys.HIGHER_FINITE_TRANSFER_COMPOSITIONS)
            arena.ledger.bump(
                _execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS,
                len(outputs),
            )
            arena.publish_runtime_composition(
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
            arena.publish_runtime_composition(
                key, RuntimeUnarySummary(a.action, a.side, UnarySpatial(*key))
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
        context = arena.prospective_summary(context_record)
        arena.publish_runtime_composition(
            key,
            RuntimeUnarySummary(
                a.action,
                a.side,
                UnaryTemporal(
                    arena.runtime_compositions[forward],
                    arena.runtime_compositions[opposite],
                    context,
                ),
            ),
            context=context_record,
        )
        arena.ledger.bump(_execution_keys.HIGHER_RUNTIME_INTERCHANGE_COMPOSITIONS)
    return arena.runtime_compositions[root]
