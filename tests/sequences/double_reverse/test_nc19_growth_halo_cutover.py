"""NC19 shared border quotient and source-authenticated segmented halo tests."""

from __future__ import annotations

import json
from random import Random
from typing import Never

import pytest

from number_compiler.api import cli
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    PHYSICAL_GROWTH_CYCLES,
    edge_phase_of_integer,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
    certified_width_moments,
)


def _step(value: int) -> int:
    return 2 * int(str(value)[::-1])


def test_single_border_growth_quotient_is_closed_on_random_admitted_words() -> None:
    assert len(set(PHYSICAL_GROWTH_CYCLES)) == 4
    assert all(sum(word) == 2 for word in PHYSICAL_GROWTH_CYCLES)
    rng = Random(0x19A7)
    prefixes = (("17",), ("17",), ("48", "49"), ("48", "49"))
    suffixes = (("68", "88"), ("42",), ("42",), ("68", "88"))
    for phase in range(4):
        word = PHYSICAL_GROWTH_CYCLES[phase]
        for j in range(1, 120):
            inner = "".join(str(rng.randrange(10)) for _ in range(j % 13))
            value = int(
                rng.choice(prefixes[phase]) + inner + rng.choice(suffixes[phase])
            )
            assert edge_phase_of_integer(value) == phase
            for expected_growth in word:
                successor = _step(value)
                assert len(str(successor)) - len(str(value)) == expected_growth
                value = successor
            assert len(str(value)) == (j % 13 + 4) + 2
            assert certified_width_moments(phase, 4).U == 2
            assert edge_phase_of_integer(value) == phase
        left_growth, right_growth = growth_ports(phase, 2)
        assert left_growth + right_growth == 2


def test_both_cli_observers_reuse_one_authenticated_defect_cone(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    import number_compiler.sequences.double_reverse.temporal_defect_period as period_module

    def prohibited_second_scan(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("second source-cone defect compilation was performed")

    monkeypatch.setattr(
        period_module, "defect_clock_cli_packet", prohibited_second_scan
    )
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                "256",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--info",
                "temporal.seed-morphism",
                "--temporal-period-samples",
                "24",
                "--temporal-defect-digits",
                "18",
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)["info"]
    direct = payload["temporal.defect-clock"]
    seed = payload["temporal.seed-morphism"]
    assert direct["status"] == "available"
    assert seed["period_observations"]["full_endpoint_suffix_verified"] is True
    assert direct["rows"] == seed["period_observations"]["rows"]
    assert (
        direct["composed_signed_action"]
        == seed["period_observations"]["composed_signed_action"]
    )
    assert direct["source_halo_segments"] == 1


def test_segmented_source_halo_not_single_sample_cones(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                "3000",
                "--max-state-bits",
                "8192",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--temporal-defect-digits",
                "24",
                "--temporal-period-samples",
                "20",
                "--temporal-period-stride",
                "32",
                "--temporal-period-max-lag",
                "12",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)["info"]["temporal.defect-clock"]
    assert result["status"] == "available"
    assert result["source_halo_segments"] == 2
    assert result["segmented_source_halo"] is True
    assert result["shared_source_halo"] is False
    assert result["local_t_squared_steps"] == 2 * 32 * (20 - 2)
    assert result["samples"] == 20
    assert result["infinite_period_certified"] is False
    # The exact temporal seam still comes from authenticated scalar probes.
    assert len(result["rows"]) == 20
    assert all(len(row["carry_first"]) == 24 for row in result["rows"])


def test_canonical_cli_repeated_request_shares_one_certificate(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api import bank_observation

    original = bank_observation.double_reverse_residue_packet
    calls: list[DoubleReverseTerm] = []

    def once(term: DoubleReverseTerm) -> dict[str, object]:
        calls.append(term)
        if len(calls) != 1:
            raise AssertionError("duplicate residue / growth-quotient source fold")
        return original(term)

    monkeypatch.setattr(bank_observation, "double_reverse_residue_packet", once)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "512",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.residue99",
                "--info",
                "temporal.residue99",
            ]
        )
        == 0
    )
    packets = json.loads(capsys.readouterr().out)["info"]
    assert tuple(packets) == ("temporal.residue99",)
    assert packets["temporal.residue99"]["target_generation"] == 512
    assert len(calls) == 1
