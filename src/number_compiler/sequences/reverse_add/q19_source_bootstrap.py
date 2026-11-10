"""Source-rooted Q19 publication used by reverse image composition."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.punctured_temporal import (
    MAX_PUNCTURED_TEMPORAL_STEPS,
)
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.source_actions import (
    ReverseActionArena,
    ReverseActionID,
)


def publish_q19_source_root(
    actions: ReverseActionArena,
    ledger: ResourceLedger,
    action: ReverseActionID,
    payload_action: ReverseActionID,
    origin: ExactSource,
    steps: int,
    owner_for_source: Callable[[ExactSource], ReversePairQ19OutputOwner],
    clear_query_output: Callable[[], None],
    *,
    owner_already_published: bool,
) -> tuple[ReverseActionID, ReversePairOutputOccurrence] | None:
    """Publish an exact decimal endpoint from a source-rooted action.

    Large decimal endpoints use the exact packed pair recurrence. Small
    startup requests retain their bounded punctured/primitive path. The return
    value carries the action and authenticated occurrence together so callers
    can publish one source-image candidate with matching duration.
    """
    if steps < 2 or actions.node(payload_action).steps != 0:
        return None
    if 64 <= steps <= MAX_PUNCTURED_TEMPORAL_STEPS and origin.base == 10:
        try:
            owner = owner_for_source(origin)
            occurrence = owner.publish_broadword_source(steps)
        except BlockContextBudgetExceeded:
            # Packed publication is an optimization. The scheduler can
            # continue through its exact child route under the remaining
            # request budget.
            if not owner_already_published:
                clear_query_output()
            return None
        cumulative = actions.compose(payload_action, action)
        if actions.node(cumulative).steps != occurrence.temporal_steps:
            raise ValueError("broadword Q19 endpoint disagrees with action")
        return cumulative, occurrence

    if steps > 4:
        return None
    owner = owner_for_source(origin)
    occurrence = owner.initial
    remaining = steps - 1
    if remaining >= 2:
        occurrence = owner.apply_punctured_pair_block(occurrence, steps=2)
        remaining -= 2
    if remaining:
        occurrence = owner.apply_pair_step(occurrence)
        remaining -= 1
    if remaining or occurrence.temporal_steps != steps:
        raise AssertionError("bounded Q19 startup published the wrong index")
    cumulative = actions.compose(payload_action, action)
    if actions.node(cumulative).steps != occurrence.temporal_steps:
        raise ValueError("bounded Q19 startup disagrees with temporal action")
    ledger.bump(_reverse_add_keys.REVERSE_Q19_ROOT_BOOTSTRAP_PAIR_STEPS, steps - 1)
    ledger.bump(_reverse_add_keys.REVERSE_Q19_ROOT_BOOTSTRAP_PUBLICATIONS)
    if steps == 3:
        ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_PUNCTURED_COMPLETED_CHILD_PUBLICATIONS
        )
    return cumulative, occurrence
