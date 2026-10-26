"""Bounded mod-99/198 return projection for the existing residue demand."""

from __future__ import annotations

import json
from collections.abc import Mapping
from typing import TypeGuard

import pytest

from number_compiler.api import cli
from number_compiler.api.bank_observation import double_reverse_residue_packet
from number_compiler.resources.metric_keys.arithmetic_fields import (
    GROWTH_ARITHMETIC_WORK,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
    ProjectedResidueTemporalQuotient,
    certified_residue_action,
    projected_residue_return_lassos,
    projected_residue_temporal_quotient,
)


def _no_endpoint(*_args: object, **_kwargs: object) -> object:
    raise AssertionError("residue quotient must not construct the full endpoint")


def _step(value: int) -> int:
    return 2 * int(str(value)[::-1])


def _literal(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = _step(value)
    return value


def _int_field(values: Mapping[str, object], name: str) -> int:
    value = values[name]
    if type(value) is not int:
        raise AssertionError(f"{name} must be an exact integer")
    return value


def _is_mapping(value: object) -> TypeGuard[Mapping[object, object]]:
    return isinstance(value, Mapping)


def _is_string_object_mapping(
    value: object,
) -> TypeGuard[Mapping[str, object]]:
    return _is_mapping(value) and all(type(key) is str for key in value)


def _mapping(value: object) -> Mapping[str, object]:
    if not _is_string_object_mapping(value):
        raise AssertionError("packet field must be a string-keyed mapping")
    return value


def test_source_residue_action_charges_arithmetic_before_period_observation() -> None:
    with DoubleReverseTerm(17442, 128) as term:
        before = term.metrics().get(GROWTH_ARITHMETIC_WORK, 0)
        prefix, action = term.temporal_residue_quotient()
        assert prefix == 0
        assert action.duration == 128
        assert term.metrics()[GROWTH_ARITHMETIC_WORK] > before


@pytest.mark.parametrize("seed", (1, 139, 196))
def test_residue_packet_publishes_source_bound_projected_return_without_endpoint(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _no_endpoint)
    generation = 128
    with DoubleReverseTerm(seed, generation) as term:
        term.temporal_engine.admit_extended_prefix(generation)
        packet = double_reverse_residue_packet(term)
        target_value = _literal(seed, generation)
        projected = _mapping(packet["projected_period"])
        assert projected["scope"] == (
            "certified border phase and mod-99/mod-198 residues only"
        )
        assert projected["full_digit_word_authority"] is False
        assert projected["width_is_periodic"] is False
        assert projected["width_growth_per_four_ticks"] == 2
        visits = _int_field(projected, "return_states_visited")
        assert 0 < visits <= 198
        assert _int_field(packet, "target_mod198") == target_value % 198

        modulus_ports = (
            ("modulo99", 99),
            ("modulo198", 198),
        )
        for port_name, modulus in modulus_ports:
            orbit = _mapping(projected[port_name])
            expected_state = target_value % modulus
            first_seen: dict[int, int] = {}
            block = 0
            value = target_value
            while expected_state not in first_seen:
                assert block <= 198
                first_seen[expected_state] = block
                assert expected_state == value % modulus
                next_value = value
                for _ in range(4):
                    next_value = _step(next_value)
                assert (
                    expected_state
                    * _int_field(orbit, "multiplier_per_return")
                    % modulus
                ) == next_value % modulus
                value = next_value
                block += 1
                expected_state = value % modulus
            transient = first_seen[expected_state]
            period = block - transient
            assert _int_field(orbit, "initial_residue") == target_value % modulus
            assert _int_field(orbit, "transient_returns") == transient
            assert _int_field(orbit, "period_returns") == period
            assert _int_field(orbit, "period_ticks") == 4 * period
            assert _int_field(orbit, "transient_ticks_upper_bound") == 4 * transient
            assert _int_field(orbit, "cycle_width_drift") == 2 * period

        inventory = term.resource_ledger.inventory()
        scratch = next(
            account for account in inventory if account.owner == term.scratch_owner
        )
        assert scratch.entries == scratch.nodes == 0
        assert term.metrics()[GROWTH_ARITHMETIC_WORK] >= visits


def test_odd_mod198_start_has_one_return_transient() -> None:
    four_step = certified_residue_action(
        phase=0,
        width=1,
        duration=4,
        source_mod99=1,
        source_mod198=1,
    )
    modulo99, modulo198, visited = projected_residue_return_lassos(
        1,
        four_step.multiplier_mod99,
        four_step.multiplier_mod198,
    )
    assert modulo198.initial_residue == 1
    assert modulo198.transient_returns == 1
    assert modulo198.period_returns > 0
    assert modulo99.transient_returns == 0
    assert visited <= 198


def test_cli_residue_projection_is_lazy_and_source_bound(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _no_endpoint)
    monkeypatch.setattr(DoubleReverseTerm, "endpoint_root", _no_endpoint)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "512",
                "--no-value",
                "--info",
                "temporal.residue99",
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = _mapping(json.loads(capsys.readouterr().out))
    info = _mapping(result["info"])
    residue = _mapping(info["temporal.residue99"])
    projected = _mapping(residue["projected_period"])
    assert result["value"] is None
    assert projected["full_digit_word_authority"] is False
    assert projected["width_is_periodic"] is False
    assert projected["scope"] == (
        "certified border phase and mod-99/mod-198 residues only"
    )


def test_projected_return_rejects_tampered_and_stale_source_actions() -> None:
    seed = int("17" + "48" * 30 + "88")
    with DoubleReverseTerm(seed, 12) as term:
        _prefix, action = term.temporal_residue_quotient()
        projected = projected_residue_temporal_quotient(
            action,
            ledger=term.resource_ledger,
            scratch_owner=term.scratch_owner,
        )
        projected.validate_source_authority()
        forged = ProjectedResidueTemporalQuotient(
            projected.source_action,
            projected.source_generation,
            projected.target_generation,
            projected.target_phase,
            projected.target_width + 1,
            projected.width_growth_per_four_ticks,
            projected.modulo99,
            projected.modulo198,
            projected.return_states_visited,
            projected.scope,
        )
        with pytest.raises(ValueError, match="authority"):
            forged.validate_source_authority()

        original_residue = action.target_mod198
        object.__setattr__(action, "target_mod198", (original_residue + 1) % 198)
        with pytest.raises(ValueError, match="authority"):
            projected.validate_source_authority()
        object.__setattr__(action, "target_mod198", original_residue)
        projected.validate_source_authority()

    with pytest.raises(ValueError, match="authority"):
        projected.validate_source_authority()
