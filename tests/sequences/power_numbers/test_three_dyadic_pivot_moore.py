from __future__ import annotations

import pytest

from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
    MAX_PIVOT_PRECISION,
    DyadicPivotMoore,
    fixed_unit_innovation_window,
    moving_unit_innovation_window,
)
from tests.support.fermat_guarded_source_oracle import (
    literal_pivot_packet,
    literal_unit_window,
)


def test_pivot_moore_ports_match_small_exact_source_oracle() -> None:
    level = 4
    offsets = (0, 1, 2, 3, 5)
    observation = (
        FermatNumberSpec(4).demand_dyadic_pivot_moore(level, offsets).observe()
    )
    source_bits, tripling, innovation, successive, unit_xor = literal_pivot_packet(
        level, offsets
    )

    assert observation.source_bits == source_bits
    assert observation.tripling_carries == tripling
    assert observation.innovation_borrows == innovation
    assert observation.successive_innovation_borrows == successive
    assert observation.aligned_unit_xor_mask == unit_xor


def test_fixed_and_moving_unit_windows_match_literal_unit_arithmetic() -> None:
    fixed = fixed_unit_innovation_window(5, 7)
    current, following = literal_unit_window(5, 7)
    assert (fixed.current_bits, fixed.next_bits) == (current, following)

    moving = moving_unit_innovation_window(4, 6)
    current, following = literal_unit_window(4, 6, offset=5)
    assert moving.unit_offset == 5
    assert (moving.current_bits, moving.next_bits) == (current, following)
    assert moving.xor_mask == current ^ following


def test_fixed_low_window_stabilizes_for_large_external_level() -> None:
    level = 1 << 300
    first = DyadicPivotMoore(level, (0, 1, 2, 3, 6))
    later = first.advance(10**50)

    initial_ports = first.observe()
    stable_ports = later.observe()
    assert stable_ports.level != initial_ports.level
    assert (
        stable_ports.offsets,
        stable_ports.source_bits,
        stable_ports.tripling_carries,
        stable_ports.innovation_borrows,
        stable_ports.successive_innovation_borrows,
        stable_ports.aligned_unit_xor_mask,
    ) == (
        initial_ports.offsets,
        initial_ports.source_bits,
        initial_ports.tripling_carries,
        initial_ports.innovation_borrows,
        initial_ports.successive_innovation_borrows,
        initial_ports.aligned_unit_xor_mask,
    )
    assert first.action_id != DyadicPivotMoore(level, (0, 2, 3, 5, 6)).action_id


def test_moving_window_refuses_before_exceeding_precision_budget() -> None:
    with pytest.raises(ValueError, match="moving-pivot-precision-budget"):
        moving_unit_innovation_window(MAX_PIVOT_PRECISION - 4, 8)

    with pytest.raises(ValueError, match="level-exceeds-Fermat-source"):
        FermatNumberSpec(4).demand_dyadic_pivot_moore(17)
