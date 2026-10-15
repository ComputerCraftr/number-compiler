"""Source-bound Mahler min-plus powering and demanded radix ports."""

from __future__ import annotations

from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def test_power_matches_repeated_min_plus_composition_and_retains_cap() -> None:
    word = MahlerSourceBoundSafetyAction.one_bit(1).then_bit(0)
    for repetitions in (0, 1, 2, 4, 8):
        powered = word.power(repetitions)
        repeated = MahlerSourceBoundSafetyAction()
        for _ in range(repetitions):
            repeated = repeated.then(word)
        assert powered == repeated
        assert powered.to_action() == repeated.to_action()
        if repetitions:
            assert powered.cap_hat is not None


def test_radix_ports_are_optional_and_share_admitted_mahler_extent() -> None:
    term = AntihydraArithmeticTerm(8, shared_cache=False)
    result = term.result()
    ordinary = associated_action(result)
    assert "source_bound_radix6_difference" not in ordinary
    assert result.ledger.counters.get(_antihydra_keys.MAHLER_RADIX_PORT_DEMANDS, 0) == 0
    demanded = associated_action(result, include_radix_ports=True)
    packet = demanded["source_bound_radix6_difference"]
    assert isinstance(packet, dict)
    assert packet["source_extent"] == result.returns
    assert packet["base"] == 6
    difference = packet["dyadic_block_difference"]
    assert isinstance(difference, tuple)
    assert difference[1] == 3
    assert demanded["scale"] == ordinary["scale"]
    assert demanded["cap"] == ordinary["cap"]
    assert result.ledger.counters[_antihydra_keys.MAHLER_RADIX_PORT_DEMANDS] == 1


def test_zero_extent_mahler_action_is_uncapped_identity() -> None:
    term = AntihydraArithmeticTerm(0, shared_cache=False)
    packet = associated_action(term.result(), include_radix_ports=True)
    assert packet["extent"] == 0
    assert packet["scale"] == {"numerator": 1, "denominator": 1}
    assert packet["offset"] == {"numerator": 0, "denominator": 1}
    assert packet["cap"] is None
