"""Negative provenance audit; it does not certify production cutover."""

from __future__ import annotations

import pytest

from devtools.verification.oracles.sequence_arithmetic import reference_successor
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)


@pytest.mark.parametrize(
    ("seed", "temporal_steps", "expected_growth"),
    ((196, 4, 1), (9999, 2, 1), (196, 20, 8)),
)
def test_recursive_radial_action_does_not_claim_authenticated_source_growth(
    seed: int,
    temporal_steps: int,
    expected_growth: int,
) -> None:
    """The generic powered action has no source-specific growth producer."""
    source_digits = digits_lsd(seed, 10)
    source_pair = tuple(
        source_digits[index] + source_digits[-index - 1]
        for index in range(len(source_digits))
    )
    expected_pair = source_pair
    for _ in range(temporal_steps - 1):
        expected_pair = reference_successor(expected_pair, 10)

    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), source_digits, base=10, maximum_steps=temporal_steps
    )
    try:
        occurrence = cutover.pair_image(temporal_steps)
        radial = cutover.actions.temporal_action(occurrence.action)
        actual_width = cutover.pair_width(occurrence)

        assert actual_width == len(expected_pair)
        assert actual_width - len(source_pair) == expected_growth
        assert radial.no_growth == temporal_steps - 1
        assert radial.growth == 0
        assert radial.growth != expected_growth
    finally:
        cutover.dispose()


def test_supplied_source_growth_composes_but_does_not_authenticate_an_occurrence() -> (
    None
):
    """The exact sum law needs source-bound primitive weights as its input."""
    first = ReverseAddCyclotomicInnovationBlock.atom((1,), 1, order=8, bits=5)
    second = ReverseAddCyclotomicInnovationBlock.atom((2,), 0, order=8, bits=5)
    third = ReverseAddCyclotomicInnovationBlock.atom((3,), 1, order=8, bits=5)

    joined = first.then(second).then(third)

    assert joined.growth == first.growth + second.growth + third.growth == 2
    assert joined.width_phase_action.delta == joined.growth % 10
