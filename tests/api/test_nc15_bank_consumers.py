"""Public bank demands preserve final coordinates and avoid endpoint publication."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli
from number_compiler.api.json_output import is_string_object_mapping
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.reverse_add.mixed_periodic_bank import MixedFrame
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_bank_boolean import (
    CoupledBooleanBankFrame,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _no_endpoint(*args: object, **kwargs: object) -> None:
    raise AssertionError("bank projection requested an unneeded full endpoint")


def test_bank_window_reads_exact_final_pairs_without_endpoint(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _no_endpoint)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "64",
                "--no-value",
                "--info",
                "spatial.bank-window",
                "--spatial-pair-bank-position",
                "0",
                "--spatial-bank-morphism-count",
                "14",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["spatial.bank-window"]
    value = 196
    for _ in range(64):
        value = 2 * int(str(value)[::-1])
    digits = str(value)
    sums = [int(digits[i]) + int(digits[-1 - i]) for i in range(14)]
    assert packet["width_out"] == len(digits)
    assert packet["final_pair_start"] == 0
    assert packet["temporal_period"] is None
    assert packet["output_words"]["eq"] == [int(total == 9) for total in sums]
    assert packet["target_mod99"] == value % 99


@pytest.mark.parametrize("family", ("2rev10", "reverse-add"))
def test_residue_compact_metadata_without_endpoint(
    family: str, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _no_endpoint)
    monkeypatch.setattr(ReverseAddPoweredTerm, "source_workspace", _no_endpoint)
    assert (
        cli.main(
            [
                family,
                "--seed",
                "173488",
                "--nth-power10",
                "2",
                "--no-value",
                "--info",
                "temporal.residue99",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    encoded = {"encoding": "power10", "exponent": 2}
    port = packet["info"]["temporal.residue99"]
    assert packet["index"] == port["index"] == encoded
    coordinate = "target_generation" if family == "2rev10" else "duration"
    assert port[coordinate] == encoded
    assert packet["value"] is None


def test_summary_does_not_demand_new_banks(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        DoubleReverseTerm, "temporal_bank_output_morphism", _no_endpoint
    )
    monkeypatch.setattr(DoubleReverseTerm, "exact_temporal_bank_window", _no_endpoint)
    monkeypatch.setattr(DoubleReverseTerm, "temporal_residue_quotient", _no_endpoint)
    monkeypatch.setattr(DoubleReverseTerm, "temporal_carry_safety", _no_endpoint)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "64",
                "--no-value",
                "--info",
                "temporal",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert packet["info"]["temporal"]["measurements"]["projection_published"] is False
    assert "temporal.carry-safety" not in packet["info"]


def test_reverse_bank_packet_projects_all_bands_from_one_coupled_frame(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9326)
    calls = 0
    original = CoupledBooleanBankFrame.from_frame

    def counted(
        cls: type[CoupledBooleanBankFrame], source: tuple[int, ...], frame: MixedFrame
    ) -> CoupledBooleanBankFrame:
        nonlocal calls
        calls += 1
        return original(source, frame)

    monkeypatch.setattr(CoupledBooleanBankFrame, "from_frame", classmethod(counted))
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                str(seed),
                "--nth",
                "12",
                "--no-value",
                "--info",
                "spatial.bank-morphism",
                "--spatial-pair-bank-position",
                "200",
                "--spatial-bank-morphism-count",
                "48",
                "--temporal-grammar-period",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["spatial.bank-morphism"]
    assert calls == 1
    assert sum(packet["five_band_counts"].values()) == 48
    assert len(packet["first_pair_coefficients"]) == 16
    phi6: object = packet["source_carry_phi6"]
    assert is_string_object_mapping(phi6)
    digits = tuple(map(int, str(seed)[::-1]))
    carry = carry_mask = gt_mask = eq_mask = 0
    place = 1
    for low, high in zip(digits, reversed(digits), strict=True):
        pair = low + high
        carry = int(pair + carry >= 10)
        carry_mask = (carry_mask + carry * place) % 70
        gt_mask = (gt_mask + int(pair > 9) * place) % 70
        eq_mask = (eq_mask + int(pair == 9) * place) % 70
        place = place * 10 % 70
    assert phi6["source_pair_width"] == len(digits)
    # The initial Q19 pair grammar emits the first normalized return.
    assert phi6["occurrence_temporal_steps"] == 1
    assert phi6["propagated_carry_mod70"] == carry_mask
    assert phi6["raw_gt_mask_mod70"] == gt_mask
    assert phi6["raw_eq_mask_mod70"] == eq_mask
    assert phi6["complete_temporal_successor_certified"] is False
    harmonic: object = packet["mod99_binary_harmonic_phi3"]
    assert is_string_object_mapping(harmonic)
    assert seed % 9 != 0
    current = seed
    # The Q19 pair grammar is issued from the original seed; 12 physical ticks
    # reach the requested term even though that grammar has temporal_steps=1.
    for _ in range(12):
        current += int(str(current)[::-1])
    assert packet["mod99"] == current % 99
    phases: list[int] = []
    for _ in range(6):
        phases.append(current % 99)
        current += int(str(current)[::-1])
    a, b, c, d, e, f = phases
    assert harmonic["initial_pair"] == [a ^ b ^ d ^ e, b ^ c ^ e ^ f]
    assert harmonic["initial_pair"] != [0, 0]
    assert harmonic["transition_matrix"] == [[0, 1], [1, 1]]
    assert harmonic["clock_unit"] == "physical-ticks"


@pytest.mark.parametrize("information", (None, "metrics", "temporal"))
def test_reverse_value_and_summaries_do_not_demand_phi6(
    information: str | None,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(
        ReversePairQ19OutputOwner, "issued_carry_phi6_packet", _no_endpoint
    )
    arguments = ["reverse-add", "--seed", "196", "--nth", "20", "--format", "json"]
    if information is not None:
        arguments.extend(("--info", information))
    assert cli.main(arguments) == 0
    payload: object = json.loads(capsys.readouterr().out)
    assert is_string_object_mapping(payload)
    assert payload["value"] == "70446464506"
