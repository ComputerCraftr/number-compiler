"""Public bank demands preserve final coordinates and avoid endpoint publication."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.reverse_add.mixed_periodic_bank import MixedFrame
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_bank_boolean import (
    CoupledBooleanBankFrame,
)
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
    seed = periodic_reverse_add_source((5, 16), seed=9323)
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
