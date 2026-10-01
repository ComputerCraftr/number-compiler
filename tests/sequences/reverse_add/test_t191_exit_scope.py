"""Check the finite D5 quotient's exact boundary before any production port."""

from __future__ import annotations

from itertools import product

from devtools.verification.oracles.sequence_arithmetic import reference_successor


def _d5_fields() -> tuple[tuple[int, ...], ...]:
    return tuple(
        (left, near, center, near, left)
        for left, near, center in product(range(19), range(19), range(0, 19, 2))
    )


def test_d5_exit_is_an_active_growth_result_and_not_a_blank_tail() -> None:
    """A D5 growth exit creates six active cells, so blank saturation cannot replace it."""
    fields = _d5_fields()
    assert len(fields) == 3610

    growing_targets: list[tuple[int, ...]] = []
    for field in fields:
        target = reference_successor(field, 10)
        if len(target) == 6:
            growing_targets.append(target)
    assert growing_targets
    assert all(target == target[::-1] for target in growing_targets)
    assert all(all(0 <= value <= 18 for value in target) for target in growing_targets)

    source = (18, 18, 18, 18, 18)
    target = reference_successor(source, 10)
    assert target == (9, 18, 18, 18, 18, 9)
    assert len(target) == 6
    assert 19 not in target  # Decimal pair-field blank is 19.
    left_region = target[:5]
    assert left_region == (9, 18, 18, 18, 18)
    assert left_region != left_region[::-1]
