"""Source-issued three-tick growth action for a bounded outer-digit guard."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from .border_carry_safety import BorderTile

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


def try_issue_growth_101(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    steps: int,
    window_digits: int,
    max_states: int,
    issue: Callable[..., CertifiedBorderGrowth],
) -> CertifiedBorderGrowth | None:
    """Issue the original source's one-digit outer action when fully admitted."""
    if source is not owner.initial or steps != 3 or window_digits != 1:
        return None
    digits = owner.initial_digits
    if len(digits) < 3 or max_states < len(digits):
        return None
    outer_sum = digits[0] + digits[-1]
    if not 14 <= outer_sum <= 17:
        return None
    # A first birth makes the next outer pair (1, sum-10); the next two
    # outer pairs are conditional on the interior carries. The width bound
    # on max_states preserves the fallback's source-reset admission limit.
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_ATTEMPTS)
    with owner.ledger.reservation(owner.scratch_owner, nodes=16):
        first = BorderTile(1, digits[-1], digits[0])
        second = BorderTile(1, 1, outer_sum - 10)
        return issue(
            owner,
            source,
            (1, 0, 1),
            1,
            2,
            outer_pairs=((first.high, first.low), (1, outer_sum - 10), None, None),
            window_tiles=(first, second, None, None),
        )
