"""Owner-level entry points for source-bound Q19 arithmetic and banks.

The public owner keeps a narrow, stable API. This module joins its exact
source handle to the radix-19 cochain, Walsh projections, and guarded temporal
authorities without transferring ownership or inferring a global future.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_interval import fold_slp_interval
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_controlled_gt_bank import SourceGuardedGTBankAction
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner
    from .q19_periodic_cone import CertifiedUniformizingCone
    from .q19_uniform_cone import CertifiedUniformCone
    from .q19_word_summary import Q19Summary
    from .radix19_cochain import Radix19CarryBlock


def pair_value_at(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    index: int,
) -> int:
    """Read one symmetric coefficient from an authenticated pair root."""
    owner.validate(occurrence)
    if type(index) is not int or not 0 <= index < occurrence.pair_width:
        raise IndexError(index)
    parity_tag_value = owner._symbol_at(occurrence.root, 0)
    parity = parity_tag_value - (2 * owner.base - 1)
    half_width = (occurrence.pair_width + parity) // 2
    half_index = index if index < half_width else occurrence.pair_width - 1 - index
    return owner._symbol_at(occurrence.root, half_index + 1)


def range_summary(
    owner: ReversePairQ19OutputOwner,
    root: int,
    begin: int,
    end: int,
    *,
    reverse: bool = False,
) -> Q19Summary:
    """Fold a pair-symbol interval through cached regions, excluding tags."""
    from .q19_word_summary import Q19Summary

    return fold_slp_interval(
        owner.arena,
        root,
        begin,
        end,
        identity=Q19Summary.identity(),
        length=lambda node_id: owner._summaries[node_id].symbols,
        full_value=lambda node_id, backwards: (
            owner._summaries[node_id].reverse
            if backwards
            else owner._summaries[node_id].forward
        ),
        compose=lambda left, right: left.then(right),
        repeat=lambda summary, count: summary.repeat(count),
        reverse=reverse,
        on_visit=lambda: owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_POINT_REGION_VISITS
        ),
    )


def digit(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    position: int,
) -> int:
    """Read one exact normalized decimal digit from an issued source root."""
    from .q19_word_summary import Q19_UPPER

    owner.validate(occurrence)
    if type(position) is not int or not 0 <= position < occurrence.output_width:
        raise IndexError(position)
    if position == occurrence.pair_width:
        return 1
    root = occurrence.root
    half = owner._summaries[root].symbols
    with owner.ledger.reservation(
        owner._scratch_owner, nodes=16 * (len(owner.arena.nodes) + 1)
    ):
        prefix = owner._range_summary(root, 0, min(position, half))
        if position > half:
            prefix = prefix.then(
                owner._range_summary(
                    root,
                    occurrence.pair_width - position,
                    occurrence.pair_width - half,
                    reverse=True,
                )
            )
        value = owner._pair_value_at(occurrence, position)
        return (value + int(prefix.domain == Q19_UPPER)) % owner.base


def digits_at(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    positions: tuple[int, ...],
) -> tuple[int, ...]:
    """Read ordered Q19 positions with one issuance check and prefix walk."""
    from .q19_word_summary import Q19_UPPER, Q19Summary

    owner.validate_issued_occurrence(occurrence)
    if type(positions) is not tuple or any(
        type(position) is not int or not 0 <= position < occurrence.output_width
        for position in positions
    ):
        raise ValueError("Q19 digit batch needs an ordered tuple of valid positions")
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BATCHED_DIGIT_REQUESTS)
    unique_positions = tuple(sorted(set(positions)))
    if not unique_positions:
        return ()
    owner.ledger.bump(
        _reverse_add_keys.REVERSE_Q19_BATCHED_DIGIT_POSITIONS,
        len(unique_positions),
    )
    root = occurrence.root
    half = owner._summaries[root].symbols
    width = occurrence.pair_width
    prefix = Q19Summary.identity()
    cursor = 0
    result: dict[int, int] = {}
    try:
        with owner.ledger.reservation(
            owner._scratch_owner, nodes=16 * (len(owner.arena.nodes) + 1)
        ):
            for position in unique_positions:
                if position == width:
                    result[position] = 1
                    cursor = position
                    continue
                boundary = min(position, half)
                if cursor < boundary:
                    prefix = prefix.then(owner._range_summary(root, cursor, boundary))
                    owner.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BATCHED_PREFIX_REGION_FOLDS
                    )
                if position > half:
                    lower = max(cursor, half)
                    if lower < position:
                        prefix = prefix.then(
                            owner._range_summary(
                                root, width - position, width - lower, reverse=True
                            )
                        )
                        owner.ledger.bump(
                            _reverse_add_keys.REVERSE_Q19_BATCHED_PREFIX_REGION_FOLDS
                        )
                value = owner._pair_value_at(occurrence, position)
                result[position] = (
                    value + int(prefix.domain == Q19_UPPER)
                ) % owner.base
                cursor = position
    except BaseException:
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BATCHED_FAILED_DIGIT_BATCHES)
        raise
    return tuple(result[position] for position in positions)


def radix19_cochain(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    z: int = 2,
    modulus: int = 5,
) -> Radix19CarryBlock:
    """Project one issued Q19 source through exact decimal normalization."""
    from .radix19_cochain import fold_source_pair_cochain

    return fold_source_pair_cochain(owner, occurrence, z=z, modulus=modulus)


def radix19_walsh64_mod5(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    channel: str,
    start: int = 0,
) -> tuple[int, ...]:
    """Read 64 source-bound pair ports and transform them over F5."""
    from .radix19_cochain import source_walsh64_mod5

    return source_walsh64_mod5(owner, occurrence, channel=channel, start=start)


def authorize_radix19_gt_bank(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    period_sizes: tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7, 8),
    window_digits: int = 6,
    max_states: int = 8192,
) -> SourceGuardedGTBankAction:
    """Join exact border growth with a source-guarded conditional bank."""
    from .mixed_periodic_bank import IncompleteMixedBorder
    from .q19_uniform_cone import UniformConeNotAuthorized

    owner.validate(occurrence)
    cochain = radix19_cochain(owner, occurrence, z=2, modulus=5)
    border = certify_border_growth(
        owner,
        occurrence,
        steps=steps,
        window_digits=window_digits,
        max_states=max_states,
    )
    if cochain.exits[0] != border.growth_word[0]:
        raise AssertionError("radix-19 carry and border growth disagree")
    if type(period_sizes) is not tuple or not period_sizes:
        raise ValueError("candidate periods must be a nonempty tuple")
    for period_size in period_sizes:
        if type(period_size) is not int or not 1 <= period_size <= 32:
            raise ValueError("candidate periods must lie in 1..32")
        try:
            return authorize_controlled_gt_bank(
                owner,
                occurrence,
                steps=steps,
                coordinate=coordinate,
                growth_control=border,
                period_size=period_size,
                max_states=max_states,
            )
        except (IncompleteMixedBorder, UniformConeNotAuthorized):
            continue
    raise UniformConeNotAuthorized(
        "no source-protected GT/F5 period matches the certified border"
    )


def authorize_temporal_cell(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
) -> CertifiedUniformCone:
    """Authorize one protected interior coefficient from the exact source."""
    from .q19_uniform_cone import authorize_uniform_cone

    return authorize_uniform_cone(owner, occurrence, steps=steps, coordinate=coordinate)


def authorize_mixed_temporal_cell(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    period_size: int = 2,
) -> CertifiedUniformizingCone:
    """Authorize a mixed periodic source core that closes to uniform."""
    from .q19_periodic_cone import authorize_uniformizing_cone

    return authorize_uniformizing_cone(
        owner,
        occurrence,
        steps=steps,
        coordinate=coordinate,
        period_size=period_size,
    )


def certify_border_growth(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    steps: int,
    window_digits: int = 2,
    max_states: int = 8192,
) -> CertifiedBorderGrowth:
    """Certify a finite source-owned growth tape, not a future period."""
    from .q19_border_control import certify_border_growth as certify

    return certify(
        owner,
        occurrence,
        steps=steps,
        window_digits=window_digits,
        max_states=max_states,
    )


def authorize_controlled_gt_bank(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    growth_control: tuple[int, ...] | CertifiedBorderGrowth,
    period_size: int = 2,
    max_states: int = 10000,
) -> SourceGuardedGTBankAction:
    """Authorize the Q19-guarded conditional GT/F5 bank for an input tape."""
    from .q19_controlled_gt_bank import authorize_controlled_gt_bank as authorize

    return authorize(
        owner,
        occurrence,
        steps=steps,
        coordinate=coordinate,
        growth_control=growth_control,
        period_size=period_size,
        max_states=max_states,
    )


__all__ = [
    "authorize_controlled_gt_bank",
    "authorize_mixed_temporal_cell",
    "authorize_radix19_gt_bank",
    "authorize_temporal_cell",
    "certify_border_growth",
    "digit",
    "digits_at",
    "pair_value_at",
    "radix19_cochain",
    "radix19_walsh64_mod5",
    "range_summary",
]
