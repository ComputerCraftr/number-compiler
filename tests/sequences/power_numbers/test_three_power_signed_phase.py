"""Source authority and unknown middle survive the positional count projection."""

from dataclasses import replace

import pytest

from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec


def test_source_phase_count_projection_retains_billion_site_unknown() -> None:
    source = FermatNumberSpec(5).demand_three_power_signed_border_action(31)
    port = source.demand_signed_phase_count_port()
    assert port.known_signed_fold == source.source_signed_known_sum
    assert port.exact_complete_fold is None
    assert port.symbolic_unknown_site_count > 10**9
    assert port.source_width == source.origin.bilateral.binary.source_digits
    for counterfeit in (replace(port), replace(port, unknown_intervals=())):
        with pytest.raises(ValueError, match="unissued"):
            _ = counterfeit.exact_complete_fold
    with pytest.raises(ValueError, match="unissued"):
        replace(source).demand_signed_phase_count_port()


def test_complete_source_phase_count_is_exact_but_not_primality() -> None:
    source = FermatNumberSpec(2).demand_three_power_signed_border_action(
        2,
        low_binary_places=3,
        high_binary_places=4,
        low_decimal_places=1,
        high_decimal_places=1,
    )
    port = source.demand_signed_phase_count_port()
    assert port.exact_complete_fold == 81 % 17
    assert port.symbolic_unknown_site_count == 0
    assert source.terminal_status == "UNKNOWN"
