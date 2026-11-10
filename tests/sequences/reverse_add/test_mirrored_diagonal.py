"""Source-bound Center11 projections over exact Q19 transitions."""

from __future__ import annotations

from collections.abc import Mapping

import pytest

from number_compiler.api.json_output import is_string_object_mapping
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.temporal_center11 import (
    Center11Action,
    half_residues11,
)
from number_compiler.sequences.reverse_add.temporal_mirrored_diagonal import (
    MAX_MIRRORED_TICKS,
    center11_interval_packet,
    center11_scratch_nodes,
)
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    SymmetricCoefficientPort,
)
from tests.support.ledger_failures import assert_empty_ledger_account
from tests.support.reference_arithmetic import literal_reverse_add


def _json_object(value: object) -> Mapping[str, object]:
    if not is_string_object_mapping(value):
        raise AssertionError("expected a JSON object with string keys")
    return value


def _integer_field(value: Mapping[str, object], name: str) -> int:
    field = value.get(name)
    if type(field) is not int:
        raise AssertionError(f"expected exact integer field {name}")
    return field


@pytest.mark.parametrize("seed", (0, 1, 79, 168, 196, 139, 10089, 999999))
@pytest.mark.parametrize("steps", (1, 2, 7, 16))
def test_center11_interval_matches_literal_half_residues(seed: int, steps: int) -> None:
    packet = center11_interval_packet(seed, steps)
    center = _json_object(packet["center11"])
    endpoint = literal_reverse_add(seed, steps)
    assert center["physical_target_halves"] == list(
        half_residues11(digits_lsd(endpoint, 10))
    )
    assert center["target_halves"] == center["physical_target_halves"]
    target_width = _integer_field(packet, "target_width")
    source_width = _integer_field(packet, "source_width")
    assert target_width == len(digits_lsd(endpoint, 10))
    assert _integer_field(packet, "width_growth") == target_width - source_width
    assert packet["repetition_authority"] == "none"


def test_center11_composes_actual_adjacent_port_actions_in_order() -> None:
    seed = 196
    digits = digits_lsd(seed, 10)
    port = SymmetricCoefficientPort.from_source_digits(digits)
    composed = Center11Action.identity(len(digits) & 1)
    initial = half_residues11(digits)
    state = (*initial, (initial[0] - initial[1]) % 11)
    cumulative = state[2]
    for _ in range(3):
        width = port.width
        center_index = width // 2
        transition = port.successor_with_carry()
        switches = transition.carry.switches
        incoming = sum(switch <= center_index for switch in switches) & 1
        outgoing = sum(switch <= center_index + 1 for switch in switches) & 1
        center_coefficient = port.half_runs[-1][0]
        step = Center11Action.from_physical_ports(
            source_width=width,
            growth=transition.carry.growth,
            center_coefficient=center_coefficient,
            carry_in=incoming,
            carry_out=outgoing,
        )
        composed = composed.then(step)
        state = step.apply(*state)
        cumulative = (cumulative + state[0] - state[1]) % 11
        assert state[2] == cumulative
        port = transition.target
    endpoint_packet = center11_interval_packet(seed, 3)
    center = _json_object(endpoint_packet["center11"])
    assert (
        list(composed.apply(*half_residues11(digits)))[:2]
        == center["physical_target_halves"]
    )
    assert composed.apply(*initial, accumulated=(initial[0] - initial[1]) % 11)[
        2
    ] == _integer_field(center, "cumulative_difference_after")


def test_seed_196_center11_tracks_initial_and_final_cumulative_difference() -> None:
    packet = center11_interval_packet(196, 256)
    center = _json_object(packet["center11"])
    assert center["source_halves"] == [8, 3]
    assert center["target_halves"] == [10, 9]
    assert center["cumulative_difference_before"] == 5
    assert center["cumulative_difference_after"] == 9


def test_center11_rejects_inconsistent_carry_ports() -> None:
    with pytest.raises(ValueError, match="outgoing carry"):
        Center11Action.from_physical_ports(
            source_width=4,
            growth=0,
            center_coefficient=9,
            carry_in=1,
            carry_out=0,
        )


def test_term_reuses_one_empty_transition_scratch_account() -> None:
    seed = 196
    generation = 32
    term = ReverseAddPoweredTerm(seed, generation, max_context_nodes=100_000)
    packet = term.temporal_mirrored_diagonal()
    scratch = assert_empty_ledger_account(
        term.resource_ledger, "reverse-center11-term-scratch"
    )
    owner_count = term.resource_ledger.owner_count
    repeated = term.temporal_mirrored_diagonal()
    repeated_scratch = assert_empty_ledger_account(
        term.resource_ledger, "reverse-center11-term-scratch"
    )
    assert repeated == packet
    assert repeated_scratch.owner == scratch.owner
    assert term.resource_ledger.owner_count == owner_count
    assert _integer_field(packet, "duration") == generation
    assert center11_scratch_nodes(term.maximum_width) > 0


def test_mirrored_observation_refuses_before_tape_expansion_when_over_budget() -> None:
    term = ReverseAddPoweredTerm(196, 32, max_context_nodes=1)
    with pytest.raises(BlockContextBudgetExceeded):
        term.temporal_mirrored_diagonal()
    assert_empty_ledger_account(term.resource_ledger, "reverse-center11-term-scratch")


def test_center11_horizon_is_bounded() -> None:
    assert MAX_MIRRORED_TICKS == 512
    with pytest.raises(ValueError, match="finite horizon"):
        center11_interval_packet(196, MAX_MIRRORED_TICKS + 1)
