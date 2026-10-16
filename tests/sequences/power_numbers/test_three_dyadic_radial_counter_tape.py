"""Fail-closed tests for the joint radial/Boolean source tape."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_dyadic_radial_counter_tape import (
    DyadicCertifiedTape,
)
from number_compiler.sequences.power_numbers.three_power_adaptive_interior import (
    AdaptiveRefinedTape,
    demand_three_power_adaptive_interior,
)
from tests.support.power_numbers import track_two_adic_source_demands


def _small_refined_tape() -> tuple[DyadicCertifiedTape, AdaptiveRefinedTape]:
    spec = FermatNumberSpec(3)
    base = spec.demand_three_power_output_tape(2, low_bits=4, leading_bits=4)
    action = spec.demand_adaptive_three_power_interior(
        2, ((0, 3),), radix_demands=((5, 1),)
    )
    return base, AdaptiveRefinedTape(base, action)


def test_radial_tape_keeps_unknown_middle_and_bounds_masks() -> None:
    tape = FermatNumberSpec(3).demand_three_power_output_tape(
        4, low_bits=8, leading_bits=8
    )
    assert tape.producer_verified
    assert not tape.complete
    with pytest.raises(ValueError, match="middle-source-bit-not-certified"):
        tape.output_window(tape.low_bits, 1)
    with pytest.raises(ValueError, match="output bit width"):
        tape.output_window(0, 10**12)
    forged = replace(tape)
    assert not forged.producer_verified
    with pytest.raises(ValueError, match="source provenance"):
        forged.output_window(0, 1)
    object.__setattr__(tape, "counter", replace(tape.counter))
    assert not tape.producer_verified


def test_adaptive_action_is_factory_sealed_and_cannot_be_copied_into_authority() -> (
    None
):
    action = demand_three_power_adaptive_interior(
        3, 2, ((0, 4),), radix_demands=((5, 1),)
    )
    assert action.producer_verified
    assert action.terminal_status == "UNKNOWN"
    forged = replace(action)
    assert not forged.producer_verified
    with pytest.raises(ValueError, match="source provenance"):
        _ = forged.signed_classes


def test_adaptive_windows_share_one_maximum_precision_source_demand(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = track_two_adic_source_demands(monkeypatch)
    action = demand_three_power_adaptive_interior(
        3, 2, ((0, 4), (8, 3)), radix_demands=((5, 1),)
    )
    assert action.producer_verified
    assert calls == [(2, 14)]


def test_adaptive_provenance_rejects_equal_but_distinct_radix_port() -> None:
    action = demand_three_power_adaptive_interior(
        3, 2, ((0, 4),), radix_demands=((5, 1),)
    )
    object.__setattr__(action, "radix_ports", (replace(action.radix_ports[0]),))
    assert not action.producer_verified
    with pytest.raises(ValueError, match="source provenance"):
        _ = action.signed_classes


def test_adaptive_rejects_equal_unissued_radix_port() -> None:
    action = demand_three_power_adaptive_interior(
        3, 2, ((0, 4),), radix_demands=((5, 1),)
    )
    copied_port = replace(action.radix_ports[0])
    assert copied_port == action.radix_ports[0]
    assert not copied_port.producer_verified
    with pytest.raises(ValueError, match="unauthenticated adaptive radix"):
        replace(action, radix_ports=(copied_port,))


def test_small_radial_and_adaptive_windows_match_exact_source_bits() -> None:
    base, refined = _small_refined_tape()
    exact_source = 3**8
    assert base.output_window(0, 4) == exact_source & 0xF
    assert base.output_window(base.high_start, base.high_bits) == (
        exact_source >> base.high_start
    )
    assert refined.output_window(8, 3) == (exact_source >> 8) & 0x7
    with pytest.raises(ValueError, match="middle-source-bit-not-certified"):
        refined.output_window(7, 2)


def test_adaptive_tape_rechecks_the_joined_source_geometry_after_field_swap() -> None:
    _, refined = _small_refined_tape()
    other_width_action = demand_three_power_adaptive_interior(
        4, 2, ((0, 3),), radix_demands=((5, 1),)
    )
    object.__setattr__(refined, "action", other_width_action)
    with pytest.raises(ValueError, match="source occurrences disagree"):
        refined.output_window(8, 1)
